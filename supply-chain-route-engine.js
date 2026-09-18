// ============================================================
// Supply-Chain Route Engine — Hierarchical Pathfinding &
// Autonomous Logistics Simulation
//
// A single-file Tampermonkey userscript (~10K lines) implementing:
//
//   1. HPA* (Hierarchical Pathfinding A*):
//      Two-tier pathfinding replacing brute-force cross-sector Dijkstra.
//      Macro graph: wormhole tiles as nodes, Floyd-Warshall all-pairs
//      shortest path, cached per seal-cycle. Micro graph: local A*
//      with Chebyshev-distance heuristic and turn-minimization
//      tiebreaker within a single sector grid fragment.
//
//   2. True AP-Density Route Simulation:
//      Terrain-aware Dijkstra computes real action-point costs per
//      tile. Route optimization via 2-opt / Or-opt local search over
//      factory supply nodes. Hard-fail policy: no Manhattan/Chebyshev
//      distance estimates — throws on missing map data (wrong-but-
//      plausible values are the most expensive failure mode to debug).
//
//   3. Supply-Chain Optimization:
//      Per-node pickup/dropoff bookkeeping with cargo-space tracking.
//      Transit Hub (stash/retrieve) support with ping-pong loop
//      prevention. Hub reload loop guard (consumables excluded from
//      deferred stash). Resupply cycle (buy res_a+res_b at hub, travel
//      to station, sell + buy res_c, return) with per-station scoring
//      and cross-sector candidate evaluation.
//
//   4. Trade Economics:
//      Curve-aware pricing projections (different models for stations
//      vs hubs). Buy/sell projection caching with direction+quantity+
//      location keys (ADR 028). Two-way arbitrage calculator.
//      Opportunities calculator with O(C*S*B) seller*buyer pair
//      evaluation, memoized to O(C*(S+B)) via Map caches.
//
//   5. DOM Abstraction Layer:
//      Normalizes two distinct trade-screen layouts (standard trade
//      vs transit-hub management) into a unified sell/buy action
//      vocabulary. Live cargo scanner with phantom-protection (detects
//      invisible cargo consuming hull space). Reality clamp syncs
//      simulation state with live page data at each step.
//
//   6. Autonomous Navigation State Machine:
//      Wormhole-aware auto-fly with multi-leg cross-sector routing.
//      Ambush detection and auto-retreat. Resume-flight-after-ambush
//      recovery. Monster sidestep helpers for the R*C nav grid.
//
//   7. Performance Instrumentation:
//      Web Worker heartbeat watchdog (ADR 024) detects main-thread
//      freezes that rAF cannot catch. Branch-attributed duration
//      guards (ADR 026) pinpoint slow code paths. Cross-page
//      persistence via GM_setValue. Zero overhead when disabled.
//
//   8. Caching & Memoization Patterns:
//      Direction-aware Map caches for O(L^2) unique pairs in O(L^3)
//      local search (ADR 027). Per-invocation GC (function-local
//      const closures). !== undefined sentinel for null/zero values.
//      LRU-style terrain version cache with deferred increment.
//
// Architecture:
//   - IIFE-scoped, no global pollution.
//   - Static -> volatile part ordering for prompt-cache optimization.
//   - Load-time dispatcher is last (no TDZ hazards).
//   - Private-repo self-update via GM_xmlhttpRequest + GitHub Contents API.
//
// Author: Systems Architect — AI Agent Architect & Engineer
// ============================================================
(function() {
    'use strict';

    // --- 1. Sector Map Static Data ---

// SECTOR_DATA: N grid fragments, each { start, cols, rows }.
// start = first tile ID in the fragment's linear range.
// Pseudocode -- real values redacted for anonymization.
const SECTOR_DATA = {
    // [REDACTED -- ~200 sector fragments with start tile IDs, cols, and rows]
    // Each entry: "S-NNN": { start: <int>, cols: <int>, rows: <int> }
    // Keyed by canonical sector name; alternate names resolved by _resolveSectorName.

      // parsedMap is populated from localStorage["logistics_static_map_data"] by
      // parseStaticMap() in the local-sector equip_f part.
      const parsedMap = {};

      // >> Sector data resolver — resolves sub-sector and alternate-name lookups
      // to their parent SECTOR_DATA entry.  map_data.txt sometimes splits a
      // single game sector into multiple grid fragments (e.g. "Fragment-0_East"
      // and "Fragment-0_West") that share the same tile-ID range but have
      // impassable walls between them.  It also uses slightly different name
      // formatting ("S001" vs "S 001") and alternate spellings ("SectorA"
      // vs "Sector-A").  _resolveSectorName returns the canonical SECTOR_DATA key,
      // or null.  getSectorData returns the {start, cols, rows} object.
     const _SECTOR_NAME_ALIASES = {
         'SectorA': 'Sector-A',
         'SectorA South': 'Sector-A',
     };
     function _resolveSectorName(name) {
         if (!name) return null;
         let data;
         try { data = SECTOR_DATA; } catch (e) { return null; }
         if (!data) return null;
         if (data[name]) return name;
         if (_SECTOR_NAME_ALIASES[name] && data[_SECTOR_NAME_ALIASES[name]])
             return _SECTOR_NAME_ALIASES[name];
         const spaced = name.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
         if (spaced !== name && data[spaced]) return spaced;
         const parent = name.replace(/ (East|West|North|South|Inner|NE|SE|NW|SW)$/, '');
         if (parent !== name && data[parent]) return parent;
         const parentSpaced = parent.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
         if (parentSpaced !== parent && data[parentSpaced]) return parentSpaced;
         return null;
     }
     function getSectorData(name) {
         const resolved = _resolveSectorName(name);
         if (!resolved) return null;
         try { return SECTOR_DATA[resolved]; } catch (e) { return null; }
     }
    // --- 2. Math & String Utilities ---
    function parseCoords(coordString) {
        const match = coordString.match(/(\d+),(\d+)/);
        return match ? { x: parseInt(match[1]), y: parseInt(match[2]) } : { x: 0, y: 0 };
    }

    function normalizeCoords(coordString) {
        const c = parseCoords(coordString || '');
        return `[${c.x},${c.y}]`;
    }

    function parseLiveCargo(str) {
        let cargo = {};
        if (!str) return cargo;
        let parts = str.split(',');
        for (let p of parts) {
            let match = p.trim().match(/^(\d+)\s+(.+)$/);
            if (match) {
                cargo[match[2].toLowerCase()] = parseInt(match[1], 10);
            }
        }
        return cargo;
    }

    function stringifyLiveCargo(cargoObj) {
        let parts = [];
        for (let k in cargoObj) {
            if (cargoObj[k] > 0) {
                let name = k.charAt(0).toUpperCase() + k.slice(1);
                parts.push(`${cargoObj[k]} ${name}`);
            }
        }
        return parts.join(', ');
    }

    // --- 3. Ground-Truth Cargo Scanner w/ Phantom Protection ---
    function syncCargoFromNav() {
        let cargoArea = document.getElementById('cargo_content') || document.getElementById('cargo');

        if (!cargoArea) {
            let banners = document.querySelectorAll('img');
            for (let i = 0; i < banners.length; i++) {
                if (banners[i].src.includes('titles/cargo')) {
                    cargoArea = banners[i].closest('td') || banners[i].closest('div') || banners[i].parentNode;
                    break;
                }
            }
        }

        if (!cargoArea) return;

        let newCargo = {};
        let imgs = cargoArea.querySelectorAll('img[src*="res/"]');

        imgs.forEach(img => {
            let name = (img.getAttribute('title') || img.getAttribute('alt') || '').toLowerCase();
            if (!name) return;

            let amt = 0;
            let sibling = (img.parentNode && img.parentNode.tagName === 'A') ? img.parentNode.nextSibling : img.nextSibling;

            if (sibling && sibling.nodeType === Node.TEXT_NODE) {
                let match = sibling.textContent.match(/^\s*[:\-]?\s*(\d+)/);
                if (match) amt = parseInt(match[1], 10);
            }
            if (amt > 0) {
                newCargo[name] = amt;
            }
        });

        let parsedSum = Object.values(newCargo).reduce((a, b) => a + b, 0);
        // Narrow the text read to the cargo panel (already located above)
        // instead of document.body.innerText, which forces a synchronous
        // full-page reflow blocking first paint. textContent avoids reflow
        // entirely; cargoArea is guaranteed non-null by the early return.
        // All three scanned patterns ("Cargo space left", "DROP CARGO",
        // "Nt in magnetic cargo hold") live inside this panel.
        let bodyText = cargoArea.textContent;

        // Parse aux_hold info: "Cargo space left: X + Yt" and "Nt in magnetic cargo hold"
        let auxHoldUsed = 0;
        let hasAuxHold = false;

        let magHoldMatch = bodyText.match(/(\d+)t\s+in\s+magnetic\s+cargo\s+hold/i);
        if (magHoldMatch) {
            auxHoldUsed = parseInt(magHoldMatch[1], 10);
            hasAuxHold = true;
        }

        let freeMatch = bodyText.match(/Cargo space left:\s*(\d+)(?:\s*\+\s*(\d+)t)?/i);
        if (freeMatch) {
            let actualFreeSpace = parseInt(freeMatch[1].replace(/,/g, ''), 10);
            if (freeMatch[2] !== undefined) {
                hasAuxHold = true;
            }

            GM_setValue('logistics_mag_scoop_used', auxHoldUsed);

            // Auto-detect regular ship capacity: regularUsed + regularFree
            if (hasAuxHold) {
                let regularUsed = Math.max(0, parsedSum - auxHoldUsed);
                let regularCapacity = regularUsed + actualFreeSpace;
                if (regularCapacity > 0) {
                    GM_setValue('logistics_ship_space', regularCapacity);
                }
            }

            let configuredMax = parseInt(document.getElementById('nav-max-cargo') ? document.getElementById('nav-max-cargo').value : GM_getValue('config_max_cargo', '200'), 10);

            let trueTakenSpace = configuredMax - actualFreeSpace;
            let invisibleCargo = trueTakenSpace - parsedSum;

            if (invisibleCargo > 0) {
                newCargo['phantom protection'] = invisibleCargo;
            }
        }

        if (Object.keys(newCargo).length > 0) {
            GM_setValue('logistics_live_cargo', stringifyLiveCargo(newCargo));
        } else if (bodyText.includes('Cargo space left') || bodyText.includes('DROP CARGO')) {
            GM_setValue('logistics_live_cargo', '');
        }
    }


    // --- 4. Buildings Tab: Bookkeeper Parser ---
    function initBookkeeperParser() {
        const checkTable = () => {
            const table = document.querySelector('.bookkeeper-overview table');
            if (table) {
                parseExtensionTable(table);

                if (GM_getValue('logistics_auto_sim', false)) {
                    GM_deleteValue('logistics_auto_sim');

                    let rawData = GM_getValue('raw_bookkeeper_data', []);
                    if (rawData.length > 0) {
                        let start = GM_getValue('config_hub_coords', '[7,16]');
                        let cap = GM_getValue('config_max_cargo', '200');
                        let toCoord = GM_getValue('config_to_coords', '');
                        let toCap = GM_getValue('config_to_cap', '');
                        let hubType = GM_getValue('config_hub_type', 'station');
                        let minTrade = GM_getValue('config_min_trade', '25');
                        let exports = GM_getValue('config_export_items', '');
                        let liveCargo = GM_getValue('logistics_live_cargo', '');

                        // Hard-fail policy: the sim throws without userloc/map
                        // data. Defer to /app/main (which always has userloc)
                        // instead of dying silently mid-observer.
                        try {
                            let optimizedData = calculateOptimalRoute(rawData, start, start, cap, toCoord, toCap, hubType, minTrade, exports, liveCargo);
                            optimizedData.history = [];
                            GM_setValue('logistics_route_v5', optimizedData);
                        } catch (e) {
                            GM_setValue('logistics_needs_recalc', true);
                            console.error('[logistics-sim] auto-sim failed (deferred to /app/main):', e);
                        }
                    }
                    window.location.href = '/app/main';
                } else if (GM_getValue('logistics_take_all_mode', false)) {
                    GM_deleteValue('logistics_take_all_mode');

                    let rawData = GM_getValue('raw_bookkeeper_data', []);
                    if (rawData.length > 0) {
                        let start = GM_getValue('config_hub_coords', '[7,16]');
                        let cap = GM_getValue('config_max_cargo', '200');
                        let toCoord = GM_getValue('config_to_coords', '');
                        let toCap = GM_getValue('config_to_cap', '');
                        let takeAllItems = GM_getValue('config_take_all_items', '');
                        let liveCargo = GM_getValue('logistics_live_cargo', '');

                        try {
                            let optimizedData = calculateTakeAllRoute(rawData, start, cap, toCoord, toCap, takeAllItems, liveCargo);
                            optimizedData.history = [];
                            GM_setValue('logistics_route_v5', optimizedData);
                        } catch (e) {
                            GM_setValue('logistics_needs_recalc', true);
                            console.error('[logistics-sim] take-all auto-sim failed (deferred to /app/main):', e);
                        }
                    }
                    window.location.href = '/app/main';
                } else if (GM_getValue('logistics_dump_all_mode', false)) {
                    GM_deleteValue('logistics_dump_all_mode');

                    let rawData = GM_getValue('raw_bookkeeper_data', []);
                    if (rawData.length > 0) {
                        let start = GM_getValue('config_hub_coords', '[7,16]');
                        let cap = GM_getValue('config_max_cargo', '200');
                        let liveCargo = GM_getValue('logistics_live_cargo', '');

                        try {
                            let optimizedData = calculateDumpAllRoute(rawData, start, cap, liveCargo);
                            optimizedData.history = [];
                            GM_setValue('logistics_route_v5', optimizedData);
                        } catch (e) {
                            GM_setValue('logistics_needs_recalc', true);
                            console.error('[logistics-sim] dump-all auto-sim failed (deferred to /app/main):', e);
                        }
                    }
                    window.location.href = '/app/main';
                }
                return true;
            }
            return false;
        };

        if (!checkTable()) {
            const observer = new MutationObserver((mutationsList, obs) => {
                if (checkTable()) obs.disconnect();
            });
            observer.observe(document.body, { childList: true, subtree: true });
        }
    }

    function parseExtensionTable(table) {
        const rawNodes = [];
        const commodityIdMap = {};

        table.querySelectorAll('thead img[src*="res/"]').forEach(img => {
            const title = img.getAttribute('title');
            if (title) commodityIdMap[title] = img.src.split('/').pop().split('.')[0];
        });

        const rows = table.querySelectorAll('tbody tr');
        for (let row of rows) {
            let locMatch = row.cells[0].innerText.match(/\[(\d+,\d+)\]/);
            if (!locMatch) continue;

            const node = { location: `[${locMatch[1]}]`, name: row.cells[1].innerText.trim(), pickups: {}, dropoffs: {} };

            for (let cell of row.cells) {
                let cellTitle = cell.getAttribute('title');
                let commodityId = commodityIdMap[cellTitle];
                if (commodityId) {
                    let cleanText = cell.innerText.replace(/[^\d\-]/g, '');
                    if (cleanText && cleanText !== '-' && cleanText !== '') {
                        let val = parseInt(cleanText, 10);
                        if (!isNaN(val) && val !== 0) {
                            if (val > 0) node.pickups[cellTitle] = { amount: val, id: commodityId };
                            if (val < 0) node.dropoffs[cellTitle] = { amount: Math.abs(val), id: commodityId };
                        }
                    }
                }
            }
            if (Object.keys(node.pickups).length > 0 || Object.keys(node.dropoffs).length > 0) {
                rawNodes.push(node);
            }
        }
        GM_setValue('raw_bookkeeper_data', rawNodes);
    }

    // --- 5. Static UI (Fallback) ---
    function injectBuildingsUI() {
        let centerCell = document.querySelector('td[style*="background-color:#00001C"][align="center"]');
        if (!centerCell) centerCell = document.querySelector('h1').parentNode.parentNode || document.body;

        let container = document.createElement('div');
        container.style.cssText = 'width: 672px; margin: 20px auto; text-align: center; font-family: Verdana, sans-serif; font-size: 12px; color: #ccc;';
        container.innerHTML = `<em>Logistics control has been moved to the Main Nav screen. Use the draggable UI there.</em>`;
        centerCell.appendChild(container);
    }

    // --- 6. Trade Screen Interceptor, Reality Sync, & UI ---

    function getTrueBaseFreeSpace() {
        let text = document.body.innerText;
        // Parse "Cargo space left: X + Yt" or "free space: X + Yt"
        // Return ONLY regular cargo space — aux_hold's +150 is reserved for
        // single-trade purchases and must not be used as a ceiling for
        // route-driven pickups (would allow aux_hold-filling transfers).
        let match = text.match(/(?:Cargo space left|Free Space):\s*(\d+)(?:\s*\+\s*(\d+)t)?/i);
        if (match) {
            return parseInt(match[1].replace(/,/g, ''), 10);
        }
        return null;
    }

    // --- 7. Trade-Screen DOM Abstraction ---
    // Standard /app/trade screens use:
    //   dropoff (ship->building): <input name="sell_<id>" id="sell_<id>">
    //   pickup  (building->ship): <input name="buy_<id>"  id="buy_<id>">
    // The Transit Hub (/app/manage) uses a different layout:
    //   dropoff: <input name="<id>_ship" id="ship_<id>">   (Ship table)
    //   pickup:  <input name="<id>_comm" id="comm_<id>">   (Building - Commodities table)
    //   No per-commodity Max column and no tr[id^="baserow"]; building free
    //   space is a single global figure ("Free space in building: Nt").
    // These helpers normalise both layouts so the rest of the trade logic can
    // treat them identically. Actions use the legacy vocabulary 'sell'
    // (dropoff) and 'buy' (pickup).

    function isTradingOutpostPage() {
        return window.location.pathname.indexOf('/app/manage') !== -1;
    }

    function tradeInputSelectorFor(action) {
        if (isTradingOutpostPage()) {
            return action === 'sell'
                ? 'input[type="text"][id^="ship_"]'
                : 'input[type="text"][id^="comm_"]';
        }
        return action === 'sell'
            ? 'input[type="text"][name^="sell_"]'
            : 'input[type="text"][name^="buy_"]';
    }

    function allTradeInputSelector() {
        if (isTradingOutpostPage()) {
            return 'input[type="text"][id^="ship_"], input[type="text"][id^="comm_"]';
        }
        return 'input[type="text"][name^="sell_"], input[type="text"][name^="buy_"]';
    }

    function classifyTradeInput(input) {
        if (!input) return null;
        if (isTradingOutpostPage()) {
            if (input.id.indexOf('ship_') === 0) return 'sell';
            if (input.id.indexOf('comm_') === 0) return 'buy';
            return null;
        }
        if (input.name.indexOf('sell_') === 0) return 'sell';
        if (input.name.indexOf('buy_') === 0) return 'buy';
        return null;
    }

    function readRowCommodityName(row) {
        if (!row) return '';
        let cells = row.querySelectorAll('td');
        if (cells.length < 2) return '';
        let clone = cells[1].cloneNode(true);
        clone.querySelectorAll('a, img').forEach(el => el.remove());
        return clone.innerText.trim();
    }

    // Locate the trade input for a given commodity display name + action.
    // Primary match is by commodity name text (robust across all screen
    // types); image-slug matching is a fallback.
    function findTradeInputForCommodity(action, commodityName) {
        if (!commodityName) return null;
        let key = commodityName.toLowerCase().trim();

        let inputs = document.querySelectorAll(allTradeInputSelector());
        for (let input of inputs) {
            if (classifyTradeInput(input) !== action) continue;
            let row = input.closest('tr');
            if (!row) continue;
            if (readRowCommodityName(row).toLowerCase() === key) return input;
        }

        // Fallback: match the commodity image by its filename stem (data.id).
        let slug = String(commodityName).trim();
        let slugVariants = [slug, slug.replace(/\s+/g, '-')];
        for (let s of slugVariants) {
            let imgs = document.querySelectorAll('img[src*="/' + s + '"]');
            for (let img of imgs) {
                let row = img.closest('tr');
                if (!row) continue;
                let input = row.querySelector(tradeInputSelectorFor(action));
                if (input) return input;
            }
        }
        return null;
    }

    function syncNodeWithReality(node) {
        if (!node) return false;
        let updated = false;

        let isBuildingTrade = window.location.pathname.includes('/app/trade');
        let isBuildingManagement = window.location.pathname.includes('/app/manage');
        let isPlanetTrade = window.location.pathname.includes('/app/trade2') || window.location.pathname.includes('/app/trade3');
        if (!isBuildingTrade && !isBuildingManagement && !isPlanetTrade) return false;

        let foundPickupKeys = new Set();
        let foundDropoffKeys = new Set();

        let inputs = document.querySelectorAll(allTradeInputSelector());

        inputs.forEach(input => {
            if (classifyTradeInput(input) !== 'buy') return; // pickups only
            let row = input.closest('tr');
            if (!row) return;
            let cells = row.querySelectorAll('td');
            if (cells.length < 4) return;

            let rawName = readRowCommodityName(row);

            let pickKey = Object.keys(node.pickups || {}).find(k => k.toLowerCase() === rawName.toLowerCase());
            let dropKey = Object.keys(node.dropoffs || {}).find(k => k.toLowerCase() === rawName.toLowerCase());
            if (pickKey) foundPickupKeys.add(pickKey.toLowerCase());
            if (dropKey) foundDropoffKeys.add(dropKey.toLowerCase());

            // Trade table columns: [0]icon [1]name [2]Amount(stock)
            // [3]Balance [4]Min [5]Max [6]Price [7]input.
            // The useMax link in cells[2] holds the authoritative stock.
            let bStock = NaN;
            let useMaxLink = row.querySelector('a[href*="useMax"]');
            if (useMaxLink) {
                let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                if (s) bStock = parseInt(s, 10);
            }
            if (isNaN(bStock) && cells.length > 2) {
                let s = cells[2].innerText.replace(/[^\d]/g, '');
                if (s) bStock = parseInt(s, 10);
            }

            // Building free space for dropoffs: Max (cells[5]) minus stock.
            // If Max is 0 (unlimited for produced goods), use the building's
            // total free space from the table footer.
            let bFree = NaN;
            if (isBuildingTrade && cells.length > 5) {
                let bCapStr = cells[5].innerText.replace(/[^\d]/g, '');
                let bCap = parseInt(bCapStr, 10);
                if (!isNaN(bCap) && bCap > 0 && !isNaN(bStock)) {
                    bFree = bCap - bStock;
                } else {
                    let baseRowEl = document.querySelector('tr[id^="baserow"]');
                    if (baseRowEl) {
                        let baseTable = baseRowEl.closest('table');
                        if (baseTable) {
                            let m = baseTable.innerText.match(/free\s*space:?\s*([\d,]+)/i);
                            if (m) bFree = parseInt(m[1].replace(/,/g, ''), 10);
                        }
                    }
                }
            } else if (isBuildingManagement && cells.length > 5) {
                let bCapStr = cells[5].innerText.replace(/[^\d]/g, '');
                let bCap = parseInt(bCapStr, 10);
                if (!isNaN(bCap) && !isNaN(bStock)) bFree = bCap - bStock;
            } else if (isPlanetTrade && cells.length > 4) {
                let bCapStr = cells[4].innerText.replace(/[^\d]/g, '');
                let bCap = parseInt(bCapStr, 10);
                if (!isNaN(bCap) && !isNaN(bStock)) bFree = bCap - bStock;
            }

            if (pickKey && !isNaN(bStock)) {
                if (node.pickups[pickKey].amount !== bStock) {
                    node.pickups[pickKey].amount = bStock;
                    updated = true;
                }
            }
            if (dropKey && !isNaN(bFree)) {
                if (node.dropoffs[dropKey].amount !== bFree) {
                    node.dropoffs[dropKey].amount = bFree;
                    updated = true;
                }
            }
        });

        // Second pass: pickups whose buy input has disappeared.
        // When stock hits 0, The game removes the buy input from that row, so
        // the input-based loop above skips it entirely. Detect depleted
        // pickups by checking whether a pickup input still exists for them.
        Object.keys(node.pickups || {}).forEach(name => {
            if (foundPickupKeys.has(name.toLowerCase())) return;
            let data = node.pickups[name];
            if (!data) return;
            let buyInput = findTradeInputForCommodity('buy', name);
            if (!buyInput) {
                if (data.amount !== 0) {
                    data.amount = 0;
                    updated = true;
                }
            }
        });

        // Second pass: dropoffs — the main loop only processes buy inputs, so
        // sell-input dropoffs are never reached.
        //
        // Two completely separate detection strategies based on page type:
        //
        // A) Transit Hub (/app/manage): The TH is a
        //    player-owned item dump. The page has NO baserow elements.
        //    Completion is detected by reading the ship-side sell row
        //    (ship_* input): when the ship stock for a commodity reaches 0,
        //    the dump is complete. Building free space is a single global
        //    figure ("Free space in building: Nt") read from the header.
        //
        // B) Standard trade (trade_a/trade_b/trade_c):
        //    These are NPC buildings where the player deliberately sells
        //    items. After a completed sell, the sell input vanishes (ship
        //    empty) but the baserow{N} row stays in the structure table.
        //    Completion is detected by reading structure stock and free space
        //    (Max − stock) from that baserow. data.id from parseExtensionTable
        //    is an image-filename slug (e.g. "res_c"), not the the game
        //    numeric ID used in baserow element IDs (e.g. baserowN), so a
        //    name-based fallback is used when the ID lookup fails.
        Object.keys(node.dropoffs || {}).forEach(name => {
            if (foundDropoffKeys.has(name.toLowerCase())) return;
            let data = node.dropoffs[name];
            if (!data) return;

            if (isBuildingManagement) {
                // >> TO: player-owned item dump
                // Ship-side stock: when 0 (or row gone), dump is complete.
                let shipStock = NaN;
                let shipInput = findTradeInputForCommodity('sell', name);
                if (shipInput) {
                    let shipRow = shipInput.closest('tr');
                    if (shipRow) {
                        let useMaxLink = shipRow.querySelector('a[href*="useMax"]');
                        if (useMaxLink) {
                            let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                            if (s !== '') shipStock = parseInt(s, 10);
                        }
                        if (isNaN(shipStock)) {
                            let cells = shipRow.querySelectorAll('td');
                            if (cells.length > 2) {
                                let s = cells[2].innerText.replace(/[^\d]/g, '');
                                if (s !== '') shipStock = parseInt(s, 10);
                            }
                        }
                    }
                }
                // Ship row gone entirely → commodity fully dumped
                if (isNaN(shipStock)) shipStock = 0;

                if (shipStock === 0 && data.amount > 0) {
                    data.amount = 0;
                    updated = true;
                }
            } else {
                // >> Standard trade: NPC building sell
                let row = document.getElementById('baserow' + data.id);
                if (!row) {
                    let baserows = document.querySelectorAll('tr[id^="baserow"]');
                    for (let br of baserows) {
                        if (readRowCommodityName(br).toLowerCase() === name.toLowerCase()) {
                            row = br;
                            break;
                        }
                    }
                }
                if (!row) return;
                let cells = row.querySelectorAll('td');
                if (cells.length < 6) return;

                let bStock = NaN;
                let useMaxLink = row.querySelector('a[href*="useMax"]');
                if (useMaxLink) {
                    let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                    if (s) bStock = parseInt(s, 10);
                }
                if (isNaN(bStock)) {
                    let s = cells[2].innerText.replace(/[^\d]/g, '');
                    if (s) bStock = parseInt(s, 10);
                }

                let bFree = NaN;
                if (!isNaN(bStock)) {
                    let bCapStr = cells[5].innerText.replace(/[^\d]/g, '');
                    let bCap = parseInt(bCapStr, 10);
                    if (!isNaN(bCap) && bCap > 0) {
                        bFree = bCap - bStock;
                        if (bFree < 0) bFree = 0;
                    } else {
                        let baseRowEl = document.querySelector('tr[id^="baserow"]');
                        if (baseRowEl) {
                            let baseTable = baseRowEl.closest('table');
                            if (baseTable) {
                                let m = baseTable.innerText.match(/free\s*space:?\s*([\d,]+)/i);
                                if (m) bFree = parseInt(m[1].replace(/,/g, ''), 10);
                            }
                        }
                    }
                }

                if (!isNaN(bFree) && bFree !== data.amount) {
                    data.amount = bFree;
                    updated = true;
                }
            }
        });

        if (updated) {
            for (let k in node.pickups) {
                if (node.pickups[k].amount <= 0) delete node.pickups[k];
            }
            for (let k in node.dropoffs) {
                if (node.dropoffs[k].amount <= 0) delete node.dropoffs[k];
            }
        }
        return updated;
    }

    function autoFillTrade(action, commodityName, amount) {
        if (!amount || amount <= 0) return;
        const input = findTradeInputForCommodity(action, commodityName);
        if (input) {
            input.value = amount;
            input.style.backgroundColor = '#004400';
            input.style.color = '#00ff00';
            input.style.fontWeight = 'bold';
            input.style.border = '1px solid #0f0';
        }
    }
// --- 8. Auto-Update ---
// (private-repo self-update via GM_xmlhttpRequest)
//
// Why this exists: Tampermonkey's native @updateURL check cannot authenticate
// against a private GitHub repo. raw.githubusercontent.com answers private-repo
// requests with 404 (not 401) when unauthenticated, and both fetch/XHR and
// browser top-level navigations strip credentials embedded in the URL (per the
// fetch spec and modern browser security policy), so there is NO way to fetch
// private raw content via a credential-embedded URL.
//
// This section does the version check itself using GM_xmlhttpRequest, which CAN
// send an explicit `Authorization: token <PAT>` header. When a newer @version
// is found, it calls the GitHub Contents API (also via GM_xmlhttpRequest with
// auth) to obtain a `download_url` — this URL contains a temporary signed token
// as a query parameter (not URL-embedded credentials), works without auth, and
// ends in .user.js so Tampermonkey intercepts the navigation and shows the
// install dialog.
//
// The read-only token + URLs are derived from the script's own @downloadURL
// (already baked with the token at build time) so there is no second source
// of truth. The token embedded here is a fine-grained PAT with read-only
// access to example-user/logistics-repo — even if extracted, it cannot push malicious updates.
//
// NOTE: this updater is itself shipped in v6.25, so v6.25 must be installed
// manually ONCE; every version thereafter updates automatically.

(function () {
    'use strict';

    // Headless test harnesses (JSDOM) don't polyfill GM_xmlhttpRequest/GM_info.
    // The updater is useless without the GM networking API — skip entirely.
    if (typeof GM_xmlhttpRequest === 'undefined') return;

    const CHECK_INTERVAL_MS = 8 * 60 * 60 * 1000; // 8 hours between auto-checks
    const LAST_CHECK_KEY = 'logistics_update_last_check';
    const SKIPPED_KEY = 'logistics_update_skipped_version';

    // Token is injected at build time by build-trading.js (replaces REDACTED_GH_TOKEN).
    // We can't extract it from GM_info.script.downloadURL because Tampermonkey
    // strips URL-embedded credentials for security.
    const GH_READ_TOKEN = 'REDACTED_GH_TOKEN';
    const RAW_BASE = 'https://raw.githubusercontent.com/example-user/logistics-repo/main/';
    const metaURL = RAW_BASE + 'trading.meta.js';
    const currentVersion = (typeof GM_info !== 'undefined' && GM_info.script && GM_info.script.version) || '0';

    console.log('[logistics-update] Init — current v' + currentVersion + ', metaURL ' + metaURL);

    function compareVersions(a, b) {
        const pa = String(a).split(/[.+~-]/).map(n => parseInt(n, 10) || 0);
        const pb = String(b).split(/[.+~-]/).map(n => parseInt(n, 10) || 0);
        const len = Math.max(pa.length, pb.length);
        for (let i = 0; i < len; i++) {
            const da = pa[i] || 0, db = pb[i] || 0;
            if (da !== db) return da - db;
        }
        return 0;
    }

    function notify(title, text, opts) {
        try {
            GM_notification(Object.assign({ title: title, text: text, timeout: 12000 }, opts || {}));
        } catch (e) {
            console.log('[logistics-update]', title, text);
        }
    }

    function fetchMeta(cb) {
        GM_xmlhttpRequest({
            method: 'GET',
            url: metaURL,
            headers: { Authorization: 'token ' + GH_READ_TOKEN },
            timeout: 15000,
            onload: function (r) {
                if (r.status >= 200 && r.status < 300) {
                    const m = (r.responseText || '').match(/@version\s+(\S+)/);
                    cb(m ? m[1] : null);
                } else {
                    console.warn('[logistics-update] meta fetch HTTP', r.status);
                    cb(null);
                }
            },
            onerror: function () { console.warn('[logistics-update] meta fetch error'); cb(null); },
            ontimeout: function () { console.warn('[logistics-update] meta fetch timeout'); cb(null); }
        });
    }

    function installUpdate(remoteVersion) {
        console.log('[logistics-update] installUpdate v' + remoteVersion);
        notify('Logistics', 'Fetching signed download link for v' + remoteVersion + '...');
        // Browsers strip credentials from URL navigations, so we can't open
        // the raw URL with token-in-URL. Instead, call the Contents API (which
        // we CAN auth via GM_xmlhttpRequest headers) to get a signed
        // download_url — a temporary URL with a token query parameter that
        // works without auth and ends in .user.js so Tampermonkey intercepts it.
        const apiUrl = 'https://api.github.com/repos/example-user/logistics-repo/contents/trading.user.js?ref=main';
        GM_xmlhttpRequest({
            method: 'GET',
            url: apiUrl,
            headers: { Authorization: 'token ' + GH_READ_TOKEN, Accept: 'application/vnd.github+json' },
            timeout: 15000,
            onload: function (r) {
                if (r.status >= 200 && r.status < 300) {
                    try {
                        const data = JSON.parse(r.responseText);
                        if (data.download_url) {
                            console.log('[logistics-update] Got signed download_url:', data.download_url);
                            GM_openInTab(data.download_url, { active: true });
                            GM_setValue(LAST_CHECK_KEY, Date.now());
                        } else {
                            console.error('[logistics-update] No download_url in API response');
                            notify('Logistics', 'Install failed: no download_url in API response.');
                        }
                    } catch (e) {
                        console.error('[logistics-update] JSON parse failed:', e);
                        notify('Logistics', 'Install failed: ' + e.message);
                    }
                } else {
                    console.error('[logistics-update] Contents API HTTP', r.status, r.responseText);
                    notify('Logistics', 'Install failed: API HTTP ' + r.status + '.');
                }
            },
            onerror: function () {
                console.error('[logistics-update] Contents API network error');
                notify('Logistics', 'Install failed: network error.');
            },
            ontimeout: function () {
                console.error('[logistics-update] Contents API timeout');
                notify('Logistics', 'Install failed: API timeout.');
            }
        });
    }

    function announceUpdate(remoteVersion) {
        const skipped = GM_getValue(SKIPPED_KEY, '');
        if (skipped === remoteVersion) return; // user dismissed this version
        const text = 'Update available: v' + currentVersion + ' → v' + remoteVersion +
            '. Click to install.';
        notify('Logistics Router', text, {
            highlight: true,
            timeout: 0,
            onclick: function () { installUpdate(remoteVersion); }
        });
        try {
            GM_registerMenuCommand('Install update v' + remoteVersion, function () {
                installUpdate(remoteVersion);
            });
            GM_registerMenuCommand('Skip update v' + remoteVersion, function () {
                GM_setValue(SKIPPED_KEY, remoteVersion);
                notify('Logistics Router', 'Update v' + remoteVersion + ' skipped. You won\'t be nagged until the next version.');
            });
        } catch (e) {}
    }

    function runCheck(force) {
        const now = Date.now();
        if (!force) {
            const last = GM_getValue(LAST_CHECK_KEY, 0);
            if (now - last < CHECK_INTERVAL_MS) return;
        }
        GM_setValue(LAST_CHECK_KEY, now);
        fetchMeta(function (remoteVersion) {
            if (!remoteVersion) return;
            console.log('[logistics-update] remote v' + remoteVersion + ' vs local v' + currentVersion);
            if (compareVersions(currentVersion, remoteVersion) < 0) {
                announceUpdate(remoteVersion);
            } else if (force) {
                notify('Logistics', 'You are up to date (v' + currentVersion + ').');
            }
        });
    }

    try {
        GM_registerMenuCommand('Check for update', function () { runCheck(true); });
    } catch (e) {}

    runCheck(false);
})();
    // --- 9. Route Economics ---
    //     Per-step credit/AP ratio.
    //
    // Computes, for each step in a simulated route, the AP spent (terrain-aware
    // travel + 5 trade action) and the credits earned/spent buying from /
    // selling to the object at that location. Prices come from the trade-tracker
    // store (flat for buildings, curve-aware for planets/stations) via the
    // existing trackerProjectBuy / trackerProjectSell helpers.
    //
    // Transit Hub steps carry no credits (player-owned stash/retrieve), so
    // their profit is 0 — only the AP cost counts.
    //
    // Matching: each tracker entry stores `userloc` (tile ID). We
    // convert that to local-sector coords via getSectorFromTileId +
    // getLocalCoordsFromTileId (same functions the tracker panel uses to
    // display coords), building a { "x,y": entry } map. Route steps store
    // [x,y] coords, so we look up by "x,y" directly. No dependence on the
    // player's userloc being readable from the page.

    // Build a { "x,y": trackerEntry } map by computing coords from each
    // entry's userloc. Returns { map, sector } where sector is the most
    // common sector among resolved entries (used for AP pathfinding).
    function buildCoordEntryMap() {
        const store = getTrackerStore();
        const map = {};
        const sectorCounts = {};
        let matched = 0, total = 0;
        for (const k in store) {
            const e = store[k];
            if (!e) continue;
            total++;
            if (e.userloc == null) continue;
            try {
                const eSector = getSectorFromTileId(e.userloc);
                if (!eSector) continue;
                const c = getLocalCoordsFromTileId(e.userloc, eSector);
                if (!c) continue;
                const key = c.x + ',' + c.y;
                const existing = map[key];
                // Prefer non-player-owned entries (NPCs with real prices).
                if (existing && !existing.playerOwned && e.playerOwned) continue;
                map[key] = e;
                matched++;
                sectorCounts[eSector] = (sectorCounts[eSector] || 0) + 1;
            } catch (err) {}
        }
        // Pick the most common sector as the player's sector.
        let bestSector = null, bestCount = 0;
        for (const s in sectorCounts) {
            if (sectorCounts[s] > bestCount) { bestCount = sectorCounts[s]; bestSector = s; }
        }
        console.log('[logistics-econ] coord map: ' + matched + '/' + total + ' entries, sector=' + bestSector + ' (' + bestCount + ' entries)');
        return { map: map, sector: bestSector };
    }

    // Resolve a commodity to its tracker resId by case-insensitive name match.
    function resolveResId(entry, rawId, name) {
        if (!entry || !entry.commodities) return null;
        const idStr = String(rawId);
        if (entry.commodities[idStr]) return idStr;
        const lname = String(name).toLowerCase();
        for (const rid in entry.commodities) {
            const c = entry.commodities[rid];
            if (c && c.name && c.name.toLowerCase() === lname) return rid;
        }
        return null;
    }

    function computeRouteEconomics(steps) {
        if (!steps || steps.length === 0) return [];

        const coordResult = buildCoordEntryMap();
        const coordMap = coordResult.map;
        const sector = coordResult.sector;
        const dijCache = {};

        // Start location: player's current coords on /app/main.
        let startLoc = null;
        try {
            const coordsEl = document.getElementById('coords');
            if (coordsEl && coordsEl.innerText) startLoc = parseCoords(coordsEl.innerText);
        } catch (e) {}
        if (!startLoc) startLoc = parseCoords(steps[0].location);

        let cumAp = 0, cumRevenue = 0, cumCost = 0;
        const results = [];
        let prevLoc = startLoc;

        for (let i = 0; i < steps.length; i++) {
            const step = steps[i];
            const loc = parseCoords(step.location);
            // Hard fail policy: simTravelAP throws when map data / sector is
            // unavailable. The caller (injectDraggableUI) wraps
            // computeRouteEconomics in try/catch and renders '?' instead.
            const travelAp = simTravelAP(prevLoc, loc, sector, dijCache);
            const apCost = travelAp + 5;

            let revenue = 0, cost = 0, tracked = false, partial = false;
            let hasPriceData = false;
            const isTo = step.destinationType === 'to';

            if (!isTo) {
                let entry = coordMap[loc.x + ',' + loc.y];
                // Station steps can land in a sector other than the one
                // coordMap was built around (or be a tracked station the
                // player hasn't visited in the current sector). Fall back
                // to a direct userloc-keyed lookup so cross-sector res_c
                // runs still get full credit accounting.
                if (!entry && step.destinationType === 'station') {
                    try {
                        const store = getTrackerStore();
                        for (const k in store) {
                            const e = store[k];
                            if (!e || e.type !== 'station' || e.userloc == null) continue;
                            const es = getSectorFromTileId(e.userloc);
                            if (!es) continue;
                            const ec = getLocalCoordsFromTileId(e.userloc, es);
                            if (ec && ec.x === loc.x && ec.y === loc.y) { entry = e; break; }
                        }
                    } catch (e2) {}
                }
                if (entry) {
                    tracked = true;
                    // Pickups = player buys FROM object.
                    for (const name in step.pickups) {
                        const d = step.pickups[name];
                        const resId = resolveResId(entry, d.id, name);
                        if (!resId) continue;
                        const proj = trackerProjectBuy(entry, resId, d.amount);
                        if (proj) {
                            cost += proj.totalCost;
                            hasPriceData = true;
                            if (proj.quantity < d.amount) partial = true;
                        }
                    }
                    // Dropoffs = player sells TH object.
                    for (const name in step.dropoffs) {
                        const d = step.dropoffs[name];
                        const resId = resolveResId(entry, d.id, name);
                        if (!resId) continue;
                        const proj = trackerProjectSell(entry, resId, d.amount);
                        if (proj) {
                            revenue += proj.totalRevenue;
                            hasPriceData = true;
                            if (proj.quantity < d.amount) partial = true;
                        }
                    }
                } else {
                    console.log('[logistics-econ] step #' + (i+1) + ' ' + step.location + ' "' + step.name + '" — no tracker entry at ' + loc.x + ',' + loc.y);
                }
            }

            const profit = revenue - cost;
            const ratio = apCost > 0 ? profit / apCost : null;
            cumAp += apCost;
            cumRevenue += revenue;
            cumCost += cost;
            const cumProfit = cumRevenue - cumCost;
            const cumRatio = cumAp > 0 ? cumProfit / cumAp : null;

            results.push({
                apCost, travelAp, revenue, cost, profit, ratio,
                cumAp, cumProfit, cumRatio,
                tracked, hasPriceData, partial, isTo
            });
            prevLoc = loc;
        }
        return results;
    }

    // --- 10. Trade Tracker ---
    //     Per-location stock & price persistence.
    //
    // Captures the ground-truth trade-screen state (stocks, min/max caps, buy/sell
    // prices, free space, credits, and the station/station pricing-formula params)
    // for every building/station/station the player opens. Keyed by `userloc`
    // (the globally-unique game tile id) under GM key `trade_tracker_v1`.
    //
    // Exposes projection helpers (projectBuy/projectSell) so the future hub-router
    // can estimate per-trade revenue and resulting stock without re-visiting.

    // GM storage key for the tracker store. Safe to declare here (rather than
    // the header) because the only load-time code is the main-execution
    // dispatcher, which is the LAST part in the concatenation — every
    // top-level const is initialized before it runs.
    const TRACKER_KEY = 'trade_tracker_v1';

    function getTrackerStore() {
        let s = GM_getValue(TRACKER_KEY, {});
        return (s && typeof s === 'object') ? s : {};
    }
    function saveTrackerStore(store) {
        GM_setValue(TRACKER_KEY, store);
    }

    function readPageVar(name) {
        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        return (typeof w[name] !== 'undefined') ? w[name] : undefined;
    }

    function getTrackerCoords() {
        const userloc = readPageVar('userloc');
        if (userloc != null) {
            const sector = getSectorFromTileId(userloc);
            if (sector) {
                const c = getLocalCoordsFromTileId(userloc, sector);
                if (c) return '[' + c.x + ',' + c.y + ']';
            }
        }
        let coords = '';
        const el = document.getElementById('coords');
        if (el && el.innerText) coords = el.innerText;
        if (!coords) coords = GM_getValue('logistics_trade_loc', '');
        return coords ? normalizeCoords(coords) : null;
    }

    function getTrackerSector() {
        const userloc = readPageVar('userloc');
        if (userloc != null) {
            const s = getSectorFromTileId(userloc);
            if (s) return s;
        }
        const host = location.hostname || '';
        const parts = host.split('.');
        return (parts.length > 0 && parts[0]) ? parts[0] : null;
    }

    function getTrackerObjectName() {
        const form = document.querySelector(
            'form[name="trade_a"], form[name="trade_b"], form[name="trade_c"]'
        );
        if (form) {
            // The first table in the form is always the header row with
            // player name (first <b>) and object name (last <b>).  Target it
            // explicitly to avoid picking up <b> surplus/resource tags from
            // nested trade tables deeper in the form.
            const firstTable = form.querySelector('table');
            if (firstTable) {
                const firstRow = firstTable.querySelector('tbody tr') || firstTable.querySelector('tr');
                if (firstRow) {
                    const bs = firstRow.querySelectorAll('b');
                    if (bs.length > 0) return bs[bs.length - 1].textContent.trim();
                }
            }
        }
        const h1a = document.querySelector('h1 a');
        return h1a ? h1a.innerText.trim() : null;
    }

    function captureTradeScreen(source) {
        const objType = readPageVar('obj_type');
        const userloc = readPageVar('userloc');
        if (!objType || userloc == null) return null;

        const resNames = readPageVar('res_names') || {};
        const amount = readPageVar('amount') || {};
        const amountMax = readPageVar('amount_max') || {};
        const amountMin = readPageVar('amount_min') || {};
        const playerBuyPrice = readPageVar('player_buy_price') || {};
        const playerSellPrice = readPageVar('player_sell_price') || {};
        const objSpace = readPageVar('obj_space');
        const objCredits = readPageVar('obj_credits');
        const playerOwned = readPageVar('player_owned');
        const ownBase = readPageVar('own_base');
        const baseP0 = readPageVar('base_p_0');
        const baseR = readPageVar('base_r');
        const baseBuyCharge = readPageVar('base_buy_charge');
        const resUpkeep = readPageVar('res_upkeep') || {};
        const resProduction = readPageVar('res_production') || {};
        const keepRes = readPageVar('keep_res') || {};
        const milliTime = readPageVar('milliTime');

        const isPlanet = objType === 'station';
        const freeSpace = isPlanet ? Infinity : (Number.isFinite(objSpace) ? objSpace : 0);

        let totalUsed = 0;
        const commodities = {};
        for (const resId in amount) {
            if (!Object.prototype.hasOwnProperty.call(amount, resId)) continue;
            const stock = parseInt(amount[resId], 10) || 0;
            totalUsed += stock;
            commodities[resId] = {
                name: resNames[resId] || ('res_' + resId),
                stock: stock,
                min: parseInt(amountMin[resId], 10) || 0,
                max: parseInt(amountMax[resId], 10) || 0,
                buyFromObjPrice: parseInt(playerBuyPrice[resId], 10) || 0,
                sellToObjPrice: parseInt(playerSellPrice[resId], 10) || 0
            };
        }
        const capacity = isPlanet ? Infinity : (freeSpace + totalUsed);

        // DOM-based min capture: amount_min page var is not populated on
        // all trade screen types. Read min from the trade table directly.
        // Column layout (buy rows): [..][Min][Max][Price][input] — Min is
        // always 3 cells before the buy input cell, regardless of whether
        // a Balance column exists (building vs station/station).
        const tradeForm = document.querySelector(
            'form[name="trade_a"], form[name="trade_b"], form[name="trade_c"]'
        );
        if (tradeForm) {
            const buyInputs = tradeForm.querySelectorAll('input[name^="buy_"]');
            for (const inp of buyInputs) {
                const rid = inp.name.substring(4);
                if (!commodities[rid]) continue;
                const row = inp.closest('tr');
                if (!row) continue;
                const cells = Array.from(row.querySelectorAll('td'));
                const inputIdx = cells.indexOf(inp.closest('td'));
                if (inputIdx < 3) continue;
                let minVal = parseInt(cells[inputIdx - 3].textContent.replace(/[^\d]/g, ''), 10);
                if (!isNaN(minVal) && minVal >= 0) commodities[rid].min = minVal;
            }
        }

        const entry = {
            userloc: userloc,
            type: objType,
            name: getTrackerObjectName(),
            coords: getTrackerCoords(),
            sector: getTrackerSector(),
            playerOwned: !!playerOwned,
            ownBase: !!ownBase,
            freeSpace: freeSpace,
            capacity: capacity,
            credits: (objCredits == null) ? null : objCredits,
            upkeep: resUpkeep,
            production: resProduction,
            keepRes: keepRes,
            pricing: (baseP0 != null) ? {
                baseP0: baseP0,
                baseR: baseR,
                baseBuyCharge: baseBuyCharge
            } : null,
            commodities: commodities,
            capturedAt: milliTime || Date.now(),
            capturedByUrl: location.pathname,
            captureSource: source || 'load'
        };

        const store = getTrackerStore();
        store[String(userloc)] = entry;
        saveTrackerStore(store);
        return entry;
    }

    // Faithful port of tradeV3 calculateBaseResPrice(d, b, f, c, e).
    // Returns total credits for `quantity` units, summed marginal prices,
    // starting from stock level `startStock`. `isBuying` = player buys FROM obj.
    function trackerBaseResPrice(baseP0, baseR, baseBuyCharge, resId, amountMax, startStock, quantity, isBuying) {
        if (quantity <= 0 || amountMax <= 0) return 0;
        const p0 = baseP0[resId] || 0;
        if (!p0) return 0;
        const price1 = 1 / baseR;
        const price2 = Math.pow(price1, -startStock / amountMax);
        const price3 = Math.pow(price1, -quantity / amountMax) - 1;
        const price4 = Math.pow(price1, -1 / amountMax) - 1;
        let total = Math.floor(p0 * price2 * price3 / price4);
        if (!isBuying) {
            total = Math.round(total * (1 - baseBuyCharge / 100));
        }
        return total;
    }

    function trackerUsesFlatPricing(entry) {
        return entry.type === 'building' || entry.playerOwned === true;
    }

    // Project buying `quantity` units FROM this object (stock decreases).
    // Respects amount_min floor. Returns null if resId not tracked.
    function trackerProjectBuy(entry, resId, quantity) {
        if (!entry) return null;
        const c = entry.commodities[resId];
        if (!c) return null;
        const qty = Math.max(0, quantity | 0);
        const buyable = Math.min(qty, Math.max(0, c.stock - c.min));
        const newStock = c.stock - buyable;
        let totalCost;
        if (trackerUsesFlatPricing(entry)) {
            totalCost = buyable * c.buyFromObjPrice;
        } else if (entry.pricing) {
            const startStock = newStock + 1;
            totalCost = trackerBaseResPrice(
                entry.pricing.baseP0, entry.pricing.baseR, entry.pricing.baseBuyCharge,
                resId, c.max || 0, startStock, buyable, true
            );
        } else {
            totalCost = buyable * c.buyFromObjPrice;
        }
        return {
            quantity: buyable,
            totalCost: totalCost,
            perUnitAvg: buyable > 0 ? Math.round(totalCost / buyable) : 0,
            newStock: newStock,
            feasible: buyable > 0
        };
    }

    // Project selling `quantity` units TH this object (stock increases).
    // Respects per-commodity amount_max cap AND shared freeSpace. Planets unlimited.
    function trackerProjectSell(entry, resId, quantity) {
        if (!entry) return null;
        const c = entry.commodities[resId];
        if (!c) return null;
        const qty = Math.max(0, quantity | 0);
        const roomInStack = (c.max > 0) ? Math.max(0, c.max - c.stock) : 0;
        // Planets have Infinity freeSpace, but JSON serialization (GM_setValue)
        // turns Infinity into null. Treat null/undefined/station as unlimited.
        const roomInSpace = (entry.type === 'station' || entry.freeSpace == null || entry.freeSpace === Infinity) ? Infinity : Math.max(0, entry.freeSpace);
        const sellable = Math.min(qty, roomInStack, roomInSpace);
        const newStock = c.stock + sellable;
        let totalRevenue;
        if (trackerUsesFlatPricing(entry)) {
            totalRevenue = sellable * c.sellToObjPrice;
        } else if (entry.pricing) {
            totalRevenue = trackerBaseResPrice(
                entry.pricing.baseP0, entry.pricing.baseR, entry.pricing.baseBuyCharge,
                resId, c.max || 0, c.stock, sellable, false
            );
        } else {
            totalRevenue = sellable * c.sellToObjPrice;
        }
        return {
            quantity: sellable,
            totalRevenue: totalRevenue,
            perUnitAvg: sellable > 0 ? Math.round(totalRevenue / sellable) : 0,
            newStock: newStock,
            feasible: sellable > 0
        };
    }

    function formatTrackerSpace(n) {
        if (n === Infinity) return '\u221e';
        if (n == null || isNaN(n)) return '?';
        return simpleNumberFormatTracker(n) + 't';
    }
    function simpleNumberFormatTracker(e) {
        let a = String(e);
        let sign = '';
        if (a.charAt(0) === '-') { a = a.substr(1); sign = '-'; }
        let out = '';
        let i = 0;
        const d = '0123456789';
        while (i < a.length && d.indexOf(a.charAt(i)) !== -1) i++;
        for (let z = i - 1; z >= 0; z--) {
            out = a.charAt(z) + out;
            if (((i - z) % 3) === 0 && z > 0) out = ',' + out;
        }
        return sign + out + a.substring(i);
    }
    function formatTrackerTime(ms) {
        if (!ms) return '?';
        const d = new Date(Number(ms));
        if (isNaN(d.getTime())) return '?';
        return d.toLocaleString();
    }
    function trackerAgeMs(ms) {
        if (!ms) return null;
        return Date.now() - Number(ms);
    }

    function injectTrackerBadge(entry) {
        const badge = document.createElement('div');
        badge.id = 'logistics-tracker-badge';
        const nComm = Object.keys(entry.commodities).length;
        const age = trackerAgeMs(entry.capturedAt);
        const ageTxt = (age != null && age >= 0)
            ? (age < 60000 ? Math.max(1, Math.round(age / 1000)) + 's ago' : Math.round(age / 60000) + 'm ago')
            : 'just now';
        badge.style.cssText = [
            'position:fixed', 'top:0', 'right:0', 'z-index:2147483647',
            'background:#001100', 'color:#88ff88', 'border:1px solid #00ff00',
            'font-family:Verdana,sans-serif', 'font-size:11px', 'font-weight:bold',
            'padding:6px 9px', 'border-radius:0 0 0 6px', 'max-width:280px',
            'box-shadow:2px 2px 8px rgba(0,0,0,0.85)', 'cursor:default',
            'line-height:1.35'
        ].join(';');
        badge.innerHTML = [
            '<div>\u2b6f TRADE TRACKER [' + entry.type + ']</div>',
            '<div style="font-weight:normal;color:#bbffbb;">' + (entry.name || '?') + '</div>',
            '<div style="font-weight:normal;">loc ' + entry.userloc + (entry.coords ? ' @ ' + entry.coords : '') + '</div>',
            '<div style="font-weight:normal;">free ' + formatTrackerSpace(entry.freeSpace) +
                ' / cap ' + formatTrackerSpace(entry.capacity) +
                ' \u00b7 ' + nComm + ' res</div>',
            '<div style="font-weight:normal;">' + (entry.credits != null ? simpleNumberFormatTracker(entry.credits) + ' cr' : '? cr') +
                ' \u00b7 ' + entry.captureSource + ' \u00b7 ' + ageTxt + '</div>'
        ].join('');
        const mount = document.body || document.documentElement;
        if (mount) mount.appendChild(badge);
        console.log('[logistics-tracker] badge injected for', entry.type, entry.userloc);
    }

    // >> Distance helpers
    // Derive the player's tile ID from the page (/app/main has unsafeWindow.userloc).
    function trackerGetPlayerTileId() {
        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        if (typeof w.userloc !== 'undefined' && w.userloc != null) {
            return parseInt(w.userloc, 10);
        }
        return null;
    }

    // Compute AP distances from player to every tracked location.
    // Dijkstra (accurate) only — NO estimation fallback. When map data is
    // missing or a target is unreachable the distance is null (rendered as
    // unknown) rather than a Chebyshev/Manhattan guess; usedFallback flags
    // that some distances could not be computed.
    // Returns { distances: { userloc: apValue | null }, playerSector, playerCoords }
    function computeTrackerDistances() {
        const playerTileId = trackerGetPlayerTileId();
        if (playerTileId == null) return { error: 'no-userloc' };

        const playerSector = getSectorFromTileId(playerTileId);
        if (!playerSector) return { error: 'no-sector' };

        const playerCoords = getLocalCoordsFromTileId(playerTileId, playerSector);
        if (!playerCoords) return { error: 'no-coords' };

        const store = getTrackerStore();
        const result = {};

        // Group same-sector entries so we run Dijkstra once per sector.
        const sameSectorEntries = [];
        for (const k in store) {
            const e = store[k];
            if (!e || e.userloc == null) { result[k] = null; continue; }
            const eSector = getSectorFromTileId(e.userloc);
            if (eSector && eSector === playerSector) {
                sameSectorEntries.push(e);
            }
        }

        // Try real Dijkstra distances for same sector.
        let dijkstraMap = null;
        let usedFallback = false;
        if (sameSectorEntries.length > 0) {
            try {
                dijkstraMap = getSectorAllDistances(playerSector, playerCoords.x, playerCoords.y);
            } catch (err) {
                console.warn('[logistics-tracker] Dijkstra failed:', err);
            }
            if (!dijkstraMap) usedFallback = true;
        }

        // Log diagnostics for first unreachable same-sector entry.
        if (dijkstraMap) {
            for (const e of sameSectorEntries) {
                const ec = getLocalCoordsFromTileId(e.userloc, playerSector);
                if (ec) {
                    const key = ec.x + ',' + ec.y;
                    if (dijkstraMap[key] === undefined) {
                        console.warn('[logistics-tracker] Dijkstra unreachable:', e.name, 'at', key,
                            'player at', playerCoords.x + ',' + playerCoords.y, 'sector', playerSector);
                    }
                }
            }
        }

        for (const k in store) {
            const e = store[k];
            if (!e || e.userloc == null) { result[k] = null; continue; }
            const eSector = getSectorFromTileId(e.userloc);
            const eCoords = eSector ? getLocalCoordsFromTileId(e.userloc, eSector) : null;
            if (!eSector || !eCoords) { result[k] = null; continue; }

            if (eSector === playerSector) {
                if (dijkstraMap) {
                    const key = eCoords.x + ',' + eCoords.y;
                    if (dijkstraMap[key] !== undefined) {
                        result[k] = dijkstraMap[key];
                    } else {
                        // Dijkstra ran but target unreachable (blocked terrain).
                        // No estimate — show unknown rather than a wrong number.
                        result[k] = null;
                        usedFallback = true;
                    }
                } else {
                    // No map data — distance unavailable (no estimate).
                    result[k] = null;
                }
            } else {
                // Cross-sector: wormhole-aware HPA* AP. Returns null
                // when no route / no map — rendered as '?' (hard-fail,
                // no estimate). try/catch mirrors the Dijkstra guard at
                // lines 367-371 so one bad entry can't abort the pass.
                try {
                    const ap = getCrossSectorAPFast(
                        playerCoords, playerSector, eCoords, eSector, null, null);
                    result[k] = (ap !== null && isFinite(ap)) ? ap : null;
                } catch (err) {
                    console.warn('[logistics-tracker] cross-sector AP failed:', e.name, err);
                    result[k] = null;
                    usedFallback = true;
                }
            }
        }
        return {
            distances: result,
            playerSector: playerSector,
            playerCoords: playerCoords,
            usedFallback: usedFallback
        };
    }

    function injectTrackerPanel() {
        const store = getTrackerStore();
        const keys = Object.keys(store);

        const uiPos = GM_getValue('logistics_tracker_ui_pos', { top: '410px', left: '6px' });

        const wrap = document.createElement('div');
        wrap.id = 'logistics-tracker-panel';
        wrap.style.cssText = [
            'position:absolute', 'top:' + uiPos.top, 'left:' + uiPos.left, 'width:360px',
            'background-color:#00001C', 'border:1px solid #44aa44',
            'font-family:Verdana,sans-serif', 'font-size:10px', 'color:#ccc',
            'z-index:9998', 'box-shadow:2px 2px 10px rgba(0,0,0,0.8)'
        ].join(';');

        const header = document.createElement('div');
        header.style.cssText = 'background:#113311;padding:5px 7px;cursor:move;font-weight:bold;color:#88ff88;border-bottom:1px solid #2a5a2a;user-select:none;';
        header.innerHTML = '\u2b6f Trade Tracker (' + keys.length + ')\u00a0\u00a0<span style="font-size:9px;color:#5a8a5a;">drag to move \u00b7 click to toggle</span>';
        wrap.appendChild(header);

        const body = document.createElement('div');
        body.style.cssText = 'padding:4px 7px;max-height:560px;overflow:auto;';
        wrap.appendChild(body);

        // >> Filter / search state
        let searchTerm = '';
        let typeFilter = 'all';
        let distanceMap = null;      // { userloc: apDistance | null }
        let sortByDistance = false;
        let distInfo = null;         // { playerSector, playerCoords }

        // >> Filter bar
        const filterBar = document.createElement('div');
        filterBar.style.cssText = 'padding:3px 0;border-bottom:1px solid #2a3a2a;margin-bottom:3px;';
        wrap.insertBefore(filterBar, body);

        const searchInput = document.createElement('input');
        searchInput.type = 'text';
        searchInput.placeholder = 'filter by name/coord/sector...';
        searchInput.style.cssText = 'width:55%;background:#001a00;color:#88ff88;border:1px solid #2a5a2a;font-size:9px;padding:2px 4px;';
        searchInput.addEventListener('input', () => {
            searchTerm = searchInput.value.toLowerCase().trim();
            renderBody();
        });
        filterBar.appendChild(searchInput);

        const typeSelect = document.createElement('select');
        typeSelect.style.cssText = 'width:38%;margin-left:3px;background:#001a00;color:#88ff88;border:1px solid #2a5a2a;font-size:9px;padding:1px;';
        typeSelect.innerHTML = '<option value="all">all types</option>' +
            '<option value="station">planets</option>' +
            '<option value="station">stations</option>' +
            '<option value="building">buildings</option>';
        typeSelect.addEventListener('change', () => {
            typeFilter = typeSelect.value;
            renderBody();
        });
        filterBar.appendChild(typeSelect);

        function updateHeader(count) {
            header.innerHTML = '\u2b6f Trade Tracker (' + count + ')\u00a0\u00a0' +
                '<span style="font-size:9px;color:#5a8a5a;">drag to move \u00b7 click to toggle</span>';
        }

        function entryMatchesFilter(e) {
            if (typeFilter !== 'all' && e.type !== typeFilter) return false;
            if (!searchTerm) return true;
            const eSec = getSectorFromTileId(e.userloc) || '';
            const eCoord = deriveDisplayCoords(e.userloc);
            const hay = ((e.name || '') + ' ' + eCoord + ' ' + eSec + ' ' + e.userloc + ' ' + (e.sector || '')).toLowerCase();
            return hay.indexOf(searchTerm) !== -1;
        }

        function deriveDisplayCoords(userloc) {
            if (userloc == null) return '?,?';
            const sector = getSectorFromTileId(userloc);
            if (!sector) return '?,?';
            const c = getLocalCoordsFromTileId(userloc, sector);
            return c ? ('[' + c.x + ',' + c.y + ']') : '?,?';
        }

        function renderBody() {
            body.innerHTML = '';
            const s = getTrackerStore();
            const ks = Object.keys(s);
            updateHeader(ks.length);
            if (ks.length === 0) {
                body.innerHTML = '<div style="color:#888;text-align:center;padding:8px;">No locations tracked yet.<br>Open a building/station/station trade screen to capture it.</div>';
                return;
            }

            // Build list of entries that pass filter.
            let entries = [];
            for (const k of ks) {
                const e = s[k];
                if (!e) continue;
                if (entryMatchesFilter(e)) entries.push(e);
            }

            // Sort.
            if (sortByDistance && distanceMap) {
                entries.sort((a, b) => {
                    const da = distanceMap[String(a.userloc)];
                    const db = distanceMap[String(b.userloc)];
                    // null (different sector) sorts to bottom, grouped by sector name.
                    if (da == null && db == null) {
                        const sa = getSectorFromTileId(a.userloc) || '???';
                        const st = getSectorFromTileId(b.userloc) || '???';
                        if (sa !== st) return sa < st ? -1 : 1;
                        return (b.capturedAt || 0) - (a.capturedAt || 0);
                    }
                    if (da == null) return 1;
                    if (db == null) return -1;
                    return da - db;
                });
            } else {
                entries.sort((a, b) => (b.capturedAt || 0) - (a.capturedAt || 0));
            }

            const showing = entries.length;
            const filtered = ks.length - showing;
            if (filtered > 0) {
                const info = document.createElement('div');
                info.style.cssText = 'color:#5a8a5a;text-align:center;padding:2px;font-size:9px;';
                info.textContent = 'showing ' + showing + ' of ' + ks.length + ' (filtered)';
                body.appendChild(info);
            }

            function buildEntryRow(e) {
                const row = document.createElement('div');
                row.style.cssText = 'border-bottom:1px dashed #2a3a2a;padding:4px 0;margin-bottom:2px;';

                const typeColor = e.type === 'station' ? '#aaffaa' : (e.type === 'station' ? '#88ccff' : '#ffcc88');
                const distVal = (distanceMap && distanceMap[String(e.userloc)] !== undefined)
                    ? distanceMap[String(e.userloc)] : null;
                const eSector = getSectorFromTileId(e.userloc);
                const eDisplayCoords = deriveDisplayCoords(e.userloc);
                const isCrossSector = distInfo && eSector && distInfo.playerSector && eSector !== distInfo.playerSector;
                let distLabel;
                if (sortByDistance && distVal != null) {
                    distLabel = ' \u00b7 <span style="color:#ffaa44;">' + distVal + ' AP</span>';
                } else if (sortByDistance && isCrossSector) {
                    distLabel = ' \u00b7 <span style="color:#666;">' + eSector + '</span>';
                } else {
                    distLabel = '';
                }

                // Compact one-line header (click to expand).
                const headDiv = document.createElement('div');
                headDiv.style.cssText = 'cursor:pointer;user-select:none;';
                const typeIcon = e.type === 'station' ? '\u25cf' : (e.type === 'station' ? '\u25b2' : '\u25a0');
                const toggleSpan = document.createElement('span');
                toggleSpan.style.cssText = 'color:#5a8a5a;font-size:9px;';
                toggleSpan.textContent = '[+]';
                headDiv.innerHTML = '<span style="color:' + typeColor + ';">' + typeIcon + '</span> ' +
                    '<span style="color:' + typeColor + ';font-weight:bold;">' + (e.name || '(unknown)') + '</span> ' +
                    '<span style="color:#666;">[' + e.type + ']</span>' +
                    '<span style="color:#888;"> ' + eDisplayCoords + '</span>' +
                    distLabel +
                    ' \u00b7 <span style="color:#aaa;">free ' + formatTrackerSpace(e.freeSpace) + '</span>' +
                    ' \u00b7 ';
                headDiv.appendChild(toggleSpan);

                const detail = document.createElement('div');
                detail.style.cssText = 'display:none;margin-top:3px;padding-left:10px;';

                headDiv.addEventListener('click', () => {
                    const open = detail.style.display !== 'none';
                    detail.style.display = open ? 'none' : 'block';
                    toggleSpan.textContent = open ? '[+]' : '[-]';
                });

                // Detail content.
                let detailHtml = '<div style="color:#888;">loc ' + e.userloc +
                    ' \u00b7 ' + eDisplayCoords +
                    (eSector ? ' \u00b7 ' + eSector : '') + '</div>';
                detailHtml += '<div style="color:#aaa;">free ' + formatTrackerSpace(e.freeSpace) +
                    ' \u00b7 cap ' + formatTrackerSpace(e.capacity) +
                    ' \u00b7 ' + (e.credits != null ? simpleNumberFormatTracker(e.credits) + ' cr' : '? cr') + '</div>';
                detailHtml += '<div style="color:#666;">' + formatTrackerTime(e.capturedAt) +
                    ' \u00b7 ' + (e.captureSource || '?') + '</div>';

                const t = document.createElement('table');
                t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;margin-top:3px;';
                t.innerHTML = '<tr style="color:#5a8a5a;">' +
                    '<th style="text-align:left;">Res</th>' +
                    '<th>stk</th><th>min</th><th>max</th><th>room</th>' +
                    '<th>buy</th><th>sell</th></tr>';
                const ids = Object.keys(e.commodities).sort((a, b) => (parseInt(a, 10) - parseInt(b, 10)));
                for (const rid of ids) {
                    const c = e.commodities[rid];
                    const room = (c.max > 0) ? Math.max(0, c.max - c.stock) : '\u221e';
                    const tr = document.createElement('tr');
                    tr.style.cssText = 'color:#bbb;';
                    tr.innerHTML = '<td>' + c.name + '</td>' +
                    '<td style="text-align:right;">' + c.stock + '</td>' +
                        '<td style="text-align:right;">' + c.min + '</td>' +
                        '<td style="text-align:right;">' + c.max + '</td>' +
                        '<td style="text-align:right;color:#88ccff;">' + room + '</td>' +
                        '<td style="text-align:right;color:#ffcc88;">' + c.buyFromObjPrice + '</td>' +
                        '<td style="text-align:right;color:#88cc88;">' + c.sellToObjPrice + '</td>';
                    t.appendChild(tr);
                }

                const del = document.createElement('button');
                del.type = 'button';
                del.textContent = 'remove';
                del.style.cssText = 'margin-top:4px;cursor:pointer;font-size:9px;background:#330000;color:#ff8888;border:1px solid #884444;';
                del.addEventListener('click', () => {
                    const cur = getTrackerStore();
                    delete cur[String(e.userloc)];
                    saveTrackerStore(cur);
                    renderBody();
                });

                detail.innerHTML = detailHtml;
                detail.appendChild(t);
                detail.appendChild(del);

                row.appendChild(headDiv);
                row.appendChild(detail);
                return row;
            }

            function isToEntry(e) {
                return e && e.type === 'building' &&
                    typeof e.name === 'string' &&
                    e.name.toLowerCase().indexOf('transit hub') !== -1;
            }

            const topLevel = [];
            const groupedBuildings = [];
            for (const e of entries) {
                if (e.type === 'building' && !isToEntry(e)) {
                    groupedBuildings.push(e);
                } else {
                    topLevel.push(e);
                }
            }

            for (const e of topLevel) {
                body.appendChild(buildEntryRow(e));
            }

            if (groupedBuildings.length > 0) {
                const grpHead = document.createElement('div');
                grpHead.style.cssText = 'cursor:pointer;user-select:none;padding:4px 0;margin-top:4px;border-top:1px solid #2a5a2a;color:#ffcc88;font-weight:bold;';
                const grpToggle = document.createElement('span');
                grpToggle.style.cssText = 'color:#5a8a5a;font-size:9px;';
                grpToggle.textContent = '[+]';
                grpHead.innerHTML = '\u25a0 Buildings (' + groupedBuildings.length + ')\u00a0\u00a0' +
                    '<span style="font-size:9px;color:#8a6a3a;font-weight:normal;">click to expand</span> ';
                grpHead.appendChild(grpToggle);

                const grpBody = document.createElement('div');
                grpBody.style.cssText = 'display:none;padding-left:10px;';

                grpHead.addEventListener('click', () => {
                    const open = grpBody.style.display !== 'none';
                    grpBody.style.display = open ? 'none' : 'block';
                    grpToggle.textContent = open ? '[+]' : '[-]';
                });

                for (const e of groupedBuildings) {
                    grpBody.appendChild(buildEntryRow(e));
                }

                body.appendChild(grpHead);
                body.appendChild(grpBody);
            }
        }

        // >> Drag logic
        let collapsed = false;
        let isDragging = false, dragMoved = false, startX = 0, startY = 0, initialX = 0, initialY = 0;

        header.addEventListener('mousedown', (e) => {
            isDragging = true;
            dragMoved = false;
            startX = e.clientX; startY = e.clientY;
            initialX = wrap.offsetLeft; initialY = wrap.offsetTop;
            e.preventDefault();
        });
        document.addEventListener('mousemove', (e) => {
            if (!isDragging) return;
            let dx = e.clientX - startX, dy = e.clientY - startY;
            if (Math.abs(dx) > 3 || Math.abs(dy) > 3) dragMoved = true;
            wrap.style.left = (initialX + dx) + 'px';
            wrap.style.top = (initialY + dy) + 'px';
        });
        document.addEventListener('mouseup', () => {
            if (!isDragging) return;
            isDragging = false;
            if (dragMoved) {
                GM_setValue('logistics_tracker_ui_pos', { top: wrap.style.top, left: wrap.style.left });
            } else {
                collapsed = !collapsed;
                applyViewVisibility();
            }
        });

        // >> Controls bar
        const controls = document.createElement('div');
        controls.style.cssText = 'padding:5px 7px;border-top:1px solid #2a5a2a;display:flex;gap:4px;align-items:center;';

        const distBtn = document.createElement('button');
        distBtn.type = 'button';
        distBtn.textContent = 'Update Distance';
        distBtn.style.cssText = 'cursor:pointer;font-size:10px;background:#001a33;color:#88ccff;border:1px solid #2a5a88;padding:3px 6px;flex:1;';
        distBtn.addEventListener('click', () => {
            distBtn.textContent = 'calculating...';
            distBtn.disabled = true;
            // Defer to next tick so UI updates.
            setTimeout(() => {
                const result = computeTrackerDistances();
                if (result.error) {
                    distBtn.textContent = 'no userloc!';
                    distBtn.disabled = false;
                    setTimeout(() => { distBtn.textContent = 'Update Distance'; }, 2000);
                    return;
                }
                distanceMap = result.distances;
                distInfo = { playerSector: result.playerSector, playerCoords: result.playerCoords, usedFallback: result.usedFallback };
                sortByDistance = true;
                renderBody();
                if (result.usedFallback) {
                    distBtn.textContent = 'Updated (some AP unavailable)';
                } else {
                    distBtn.textContent = 'Distance updated';
                }
                distBtn.disabled = false;
                setTimeout(() => { distBtn.textContent = 'Update Distance'; }, 3000);
            }, 10);
        });
        controls.appendChild(distBtn);

        const clearBtn = document.createElement('button');
        clearBtn.type = 'button';
        clearBtn.textContent = 'Clear all';
        clearBtn.style.cssText = 'cursor:pointer;font-size:10px;background:#330000;color:#ffaaaa;border:1px solid #884444;padding:3px 6px;flex:0;';
        clearBtn.addEventListener('click', () => {
            if (confirm('Clear ALL tracked trade locations? This cannot be undone.')) {
                saveTrackerStore({});
                distanceMap = null;
                sortByDistance = false;
                renderBody();
            }
        });
        controls.appendChild(clearBtn);
        wrap.appendChild(controls);

        // >> Tab bar: Locations | Item Search
        let activeTab = 'locations';
        const tabBar = document.createElement('div');
        tabBar.style.cssText = 'display:flex;border-bottom:1px solid #2a5a2a;';
        wrap.insertBefore(tabBar, filterBar);

        function makeTrackerTabBtn(label, tabId) {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.textContent = label;
            btn.dataset.tab = tabId;
            btn.style.cssText = 'flex:1;cursor:pointer;font-size:10px;padding:4px 8px;border:none;border-bottom:2px solid transparent;background:#0a1a0a;color:#5a8a5a;';
            btn.addEventListener('click', () => switchTab(tabId));
            return btn;
        }
        const locTabBtn = makeTrackerTabBtn('Locations', 'locations');
        const itemTabBtn = makeTrackerTabBtn('Item Search', 'itemsearch');
        tabBar.appendChild(locTabBtn);
        tabBar.appendChild(itemTabBtn);

        // >> Item Search view
        const itemSearchView = document.createElement('div');
        itemSearchView.style.cssText = 'padding:4px 7px;display:none;';
        wrap.insertBefore(itemSearchView, body);

        const itemSearchInput = document.createElement('input');
        itemSearchInput.type = 'text';
        itemSearchInput.placeholder = 'search item name...';
        itemSearchInput.style.cssText = 'width:100%;box-sizing:border-box;background:#001a00;color:#88ff88;border:1px solid #2a5a2a;font-size:9px;padding:2px 4px;margin-bottom:4px;';
        let itemSearchTerm = '';
        let itemSearchDistTried = false;
        itemSearchInput.addEventListener('input', () => {
            itemSearchTerm = itemSearchInput.value.toLowerCase().trim();
            renderItemSearch();
        });
        itemSearchView.appendChild(itemSearchInput);

        const itemSearchResults = document.createElement('div');
        itemSearchResults.style.cssText = 'max-height:480px;overflow:auto;';
        itemSearchView.appendChild(itemSearchResults);

        itemSearchResults.addEventListener('click', (ev) => {
            const el = ev.target.closest('.tracker-item-fly');
            if (!el) return;
            const loc = parseInt(el.dataset.loc, 10);
            if (!loc) return;
            const sector = getSectorFromTileId(loc);
            if (!sector) return;
            const coords = getLocalCoordsFromTileId(loc, sector);
            if (!coords) return;
            try {
                flyToCoords({ x: coords.x, y: coords.y, sector: sector }, el.textContent + ' ' + deriveDisplayCoords(loc));
            } catch (err) { console.error('[logistics-tracker] fly error:', err); }
        });

        function applyViewVisibility() {
            tabBar.style.display = collapsed ? 'none' : 'flex';
            const showLoc = !collapsed && activeTab === 'locations';
            const showItem = !collapsed && activeTab === 'itemsearch';
            filterBar.style.display = showLoc ? 'block' : 'none';
            body.style.display = showLoc ? 'block' : 'none';
            controls.style.display = showLoc ? 'flex' : 'none';
            itemSearchView.style.display = showItem ? 'block' : 'none';
        }

        function switchTab(tabId) {
            activeTab = tabId;
            [locTabBtn, itemTabBtn].forEach(btn => {
                const on = btn.dataset.tab === tabId;
                btn.style.borderBottom = on ? '2px solid #88ff88' : '2px solid transparent';
                btn.style.color = on ? '#aaffaa' : '#5a8a5a';
                btn.style.background = on ? '#113311' : '#0a1a0a';
            });
            applyViewVisibility();
            if (tabId === 'itemsearch') renderItemSearch();
        }

        // >> Item Search renderer
        // Lists every tracked location carrying the searched commodity,
        // sorted by AP distance (closest first); null-AP (cross-sector /
        // no map) grouped last. Reuses distanceMap; computes it lazily
        // (on-demand, deferred via setTimeout) if not yet populated — no
        // heavy work at load time. Unknown AP renders '?' (hard-fail
        // policy: no estimates).
        function renderItemSearch() {
            const r = itemSearchResults;
            r.innerHTML = '';
            const s = getTrackerStore();
            const ks = Object.keys(s);
            if (ks.length === 0) {
                r.innerHTML = '<div style="color:#888;text-align:center;padding:8px;">No locations tracked yet.</div>';
                return;
            }
            if (!itemSearchTerm) {
                r.innerHTML = '<div style="color:#5a8a5a;text-align:center;padding:8px;">Type an item name to search tracked locations.</div>';
                return;
            }

            const matches = [];
            for (const k of ks) {
                const e = s[k];
                if (!e || !e.commodities) continue;
                for (const rid in e.commodities) {
                    const c = e.commodities[rid];
                    if (!c || !c.name) continue;
                    if (c.name.toLowerCase().indexOf(itemSearchTerm) === -1) continue;
                    if ((c.stock - (c.min || 0)) <= 0) continue;
                    matches.push({ entry: e, com: c });
                }
            }
            if (matches.length === 0) {
                r.innerHTML = '<div style="color:#888;text-align:center;padding:8px;">No items matching "' + itemSearchTerm + '".</div>';
                return;
            }

            // Lazy distance compute: one-shot, deferred so the
            // "calculating..." state paints first. If compute fails
            // (no userloc / no map) distanceMap stays null and AP
            // renders '?' below — no estimates.
            if (!distanceMap && !itemSearchDistTried) {
                itemSearchDistTried = true;
                r.innerHTML = '<div style="color:#8a6a3a;text-align:center;padding:8px;">Calculating AP distances...</div>';
                setTimeout(() => {
                    const result = computeTrackerDistances();
                    if (!result.error) {
                        distanceMap = result.distances;
                        distInfo = { playerSector: result.playerSector, playerCoords: result.playerCoords, usedFallback: result.usedFallback };
                    }
                    renderItemSearch();
                }, 10);
                return;
            }

            matches.sort((a, b) => {
                const da = distanceMap ? distanceMap[String(a.entry.userloc)] : null;
                const db = distanceMap ? distanceMap[String(b.entry.userloc)] : null;
                if (da == null && db == null) return (a.entry.name || '') < (b.entry.name || '') ? -1 : 1;
                if (da == null) return 1;
                if (db == null) return -1;
                return da - db;
            });

            const t = document.createElement('table');
            t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;';
            t.innerHTML = '<tr style="color:#5a8a5a;">' +
                '<th style="text-align:left;">Item</th>' +
                '<th style="text-align:left;">From</th>' +
                '<th>Sector</th>' +
                '<th>AP</th>' +
                '<th>avail</th>' +
                '<th>buy</th>' +
                '<th>sell</th></tr>';
            for (const m of matches) {
                const e = m.entry;
                const c = m.com;
                const typeColor = e.type === 'station' ? '#aaffaa' : (e.type === 'station' ? '#88ccff' : '#ffcc88');
                const typeIcon = e.type === 'station' ? '\u25cf' : (e.type === 'station' ? '\u25b2' : '\u25a0');
                const eSector = getSectorFromTileId(e.userloc) || '?';
                const eCoords = deriveDisplayCoords(e.userloc);
                const distVal = distanceMap ? distanceMap[String(e.userloc)] : null;
                const apTxt = (distVal != null)
                    ? '<span style="color:#ffaa44;">' + distVal + '</span>'
                    : '<span style="color:#666;">?</span>';
                const tr = document.createElement('tr');
                tr.style.cssText = 'border-bottom:1px dashed #2a3a2a;color:#bbb;';
                tr.innerHTML = '<td style="color:#ffcc77;">' + c.name + '</td>' +
                    '<td><span style="color:' + typeColor + ';">' + typeIcon + '</span> ' +
                        '<span class="tracker-item-fly" data-loc="' + e.userloc + '" title="Click to fly here" style="color:' + typeColor + ';cursor:pointer;text-decoration:underline;">' + (e.name || '?') + '</span>' +
                        ' <span style="color:#666;">' + eCoords + '</span></td>' +
                    '<td style="color:#888;">' + eSector + '</td>' +
                    '<td style="text-align:right;">' + apTxt + '</td>' +
                    '<td style="text-align:right;">' + Math.max(0, c.stock - (c.min || 0)) + '</td>' +
                    '<td style="text-align:right;color:#ffaa55;">' + c.buyFromObjPrice + '</td>' +
                    '<td style="text-align:right;color:#88cc88;">' + c.sellToObjPrice + '</td>';
                t.appendChild(tr);
            }
            r.appendChild(t);
        }

        renderBody();
        switchTab('locations');
        const mount = document.body || document.documentElement;
        if (mount) mount.appendChild(wrap);
        console.log('[logistics-tracker] panel injected on', currentPath, 'with', keys.length, 'locations');
    }

    // --- 11. QOL Single-Step Advancer ---

    // >> Performance instrumentation (R1 time-budget measurement — temporary, remove after data collected)
    function __perfMark(label) {
        if (!GM_getValue('logistics_perf_enabled', false)) return;
        let m = GM_getValue('logistics_perf_marks', []);
        m.push({ l: label, t: Date.now(), p: location.pathname });
        GM_setValue('logistics_perf_marks', m);
    }

    function __perfReport() {
        let m = GM_getValue('logistics_perf_marks', []);
        if (!m.length) {
            let last = GM_getValue('logistics_perf_last_report', '');
            if (last) { console.log('[perf] no new marks. Last report:\n' + last); }
            else { console.log('[perf] no marks collected'); }
            return;
        }
        let lines = [];
        lines.push('Timing breakdown (' + m.length + ' marks):');
        for (let i = 1; i < m.length; i++) {
            let dt = m[i].t - m[i - 1].t;
            let cross = m[i - 1].p !== m[i].p ? ' [CROSS-PAGE]' : '';
            lines.push('  ' + i + ': ' + m[i - 1].l + ' \u2192 ' + m[i].l + ': ' + dt + 'ms' + cross);
        }
        let report = lines.join('\n');
        GM_setValue('logistics_perf_last_report', report);
        console.group('[perf] Timing breakdown (' + m.length + ' marks)');
        for (let i = 1; i < m.length; i++) {
            let dt = m[i].t - m[i - 1].t;
            let cross = m[i - 1].p !== m[i].p ? ' [CROSS-PAGE]' : '';
            console.log('  ' + i + ': ' + m[i - 1].l + ' \u2192 ' + m[i].l + ': ' + dt + 'ms' + cross);
        }
        console.groupEnd();
        GM_setValue('logistics_perf_marks', []);
    }

    function __perfLastReport() {
        let last = GM_getValue('logistics_perf_last_report', '');
        if (last) console.log('[perf] Last report:\n' + last);
        else console.log('[perf] no report stored yet');
    }

    let __perfOn = GM_getValue('logistics_perf_enabled', false);
    function __perfEnabled(on) {
        __perfOn = on;
        GM_setValue('logistics_perf_enabled', on);
        if (!on) {
            if (__watchdogWorker) { __watchdogWorker.terminate(); __watchdogWorker = null; __watchdogRunning = false; }
            GM_setValue('logistics_perf_marks', []);
            GM_setValue('logistics_perf_heavy_log', []);
            __heavyLog.length = 0;
        }
        if (on) { GM_setValue('logistics_perf_heavy_log', []); __heavyLog.length = 0; __startWatchdog(); }
        console.log('[perf] instrumentation ' + (on ? 'ENABLED' : 'disabled'));
    }

    // >> Web Worker heartbeat watchdog + heavy-op attribution (ADR 024, supersedes ADR 022)
    // Measurement only — no behavior change. Inert unless __perfEnabled(true).
    // A Web Worker runs a 100ms setInterval independent of the main thread:
    // when the main thread freezes, rAF heartbeats stop, the worker detects
    // the gap, and records a "frame block" attributed to __currentOp (a
    // lingering label set at heavy-fn entry, never cleared). Blocks persist
    // to indexedDB so a hard freeze (tab crash) can be recovered on next load.
    // __heavyLog: synchronous duration guards for the 3× optimizeFactoryRuns
    // call sites, hpaCompile call site, and hpaGetTable L1/L2/L3 branch returns
    // (ADR 026). Cross-page persisted via GM_setValue on pagehide (ADR 026).
    const __HEAVY_THRESHOLD  = 50;
    const __LOG_CAP = 200;
    let __currentOp = 'idle';
    const __heavyLog = __perfOn ? (GM_getValue('logistics_perf_heavy_log', []) || []) : [];

    function __setOp(name) { if (__perfOn) __currentOp = name; }
    function __heavyT0(name) { __setOp(name); return performance.now(); }
    function __heavyT1(name, t0) {
        if (!__perfOn) return;
        const dt = performance.now() - t0;
        if (dt >= __HEAVY_THRESHOLD) {
            __heavyLog.push({ op: name, ms: +dt.toFixed(1), t: Date.now(), path: location.pathname });
            if (__heavyLog.length > __LOG_CAP) __heavyLog.shift();
        }
    }

    let __watchdogWorker = null;
    let __watchdogRunning = false;

    const __WORKER_CODE = `
let blocks = [];
let lastHb = 0, lastOp = '', lastPath = '';
let blkStart = 0;
let lastPersist = 0;
const THRESH = 100;
const CAP = 200;
let db = null;
function openDB() {
    try {
        const req = indexedDB.open('logistics_perf', 1);
        req.onupgradeneeded = function(e) { e.target.result.createObjectStore('blocks', {autoIncrement: true}); };
        req.onsuccess = function(e) { db = e.target.result; };
        req.onerror = function() { db = null; };
    } catch (err) { db = null; }
}
function persist() {
    if (!db) return;
    try {
        const tx = db.transaction('blocks', 'readwrite');
        const store = tx.objectStore('blocks');
        store.clear();
        for (let i = 0; i < blocks.length; i++) store.add(blocks[i]);
    } catch (err) {}
}
openDB();
setInterval(function() {
    if (lastHb === 0) return;
    const now = Date.now();
    const gap = now - lastHb;
    if (gap >= THRESH && blkStart === 0) blkStart = lastHb;
    if (blkStart > 0) {
        const ip = {ms: now - blkStart, op: lastOp, path: lastPath, t: blkStart, ip: true};
        let idx = -1;
        for (let i = blocks.length - 1; i >= 0; i--) { if (blocks[i].ip && blocks[i].t === blkStart) { idx = i; break; } }
        if (idx >= 0) blocks[idx] = ip; else blocks.push(ip);
        if (blocks.length > CAP) blocks.shift();
        if (now - lastPersist > 500) { persist(); lastPersist = now; }
    }
}, 100);
self.onmessage = function(e) {
    const m = e.data;
    if (m.type === 'heartbeat') {
        const now = Date.now();
        if (blkStart > 0) {
            blocks.push({ms: now - blkStart, op: m.op, path: m.path, t: blkStart});
            if (blocks.length > CAP) blocks.shift();
            blkStart = 0;
            persist();
        }
        lastHb = now; lastOp = m.op; lastPath = m.path;
    } else if (m.type === 'hidden') {
        lastHb = 0; blkStart = 0;
    } else if (m.type === 'dump') {
        self.postMessage({type:'dump', blocks: blocks.slice(), ip: blkStart > 0 ? {op: lastOp, path: lastPath, start: blkStart} : null});
    } else if (m.type === 'clear') {
        blocks = [];
        persist();
    }
};
`;

    function __startWatchdog() {
        if (__watchdogRunning || !__perfOn) return;
        if (typeof Worker === 'undefined' || typeof Blob === 'undefined' || typeof URL === 'undefined' || typeof URL.createObjectURL !== 'function') {
            console.warn('[perf-watchdog] Worker/Blob/URL.createObjectURL unavailable — watchdog disabled (heavyLog still active)');
            return;
        }
        try {
            const blob = new Blob([__WORKER_CODE], {type: 'application/javascript'});
            const url = URL.createObjectURL(blob);
            __watchdogWorker = new Worker(url);
            __watchdogRunning = true;
            const heartbeat = () => {
                if (!__watchdogRunning) return;
                if (document.visibilityState === 'visible') {
                    __watchdogWorker.postMessage({type:'heartbeat', op: __currentOp, path: location.pathname});
                } else {
                    __watchdogWorker.postMessage({type:'hidden'});
                }
                requestAnimationFrame(heartbeat);
            };
            requestAnimationFrame(heartbeat);
            document.addEventListener('visibilitychange', () => {
                if (document.visibilityState === 'hidden' && __watchdogWorker) {
                    __watchdogWorker.postMessage({type:'hidden'});
                }
            });
            window.addEventListener('pagehide', () => {
                if (__perfOn) GM_setValue('logistics_perf_heavy_log', __heavyLog);
            });
        } catch (e) {
            console.warn('[perf-watchdog] Worker creation failed:', e);
            __watchdogWorker = null;
            __watchdogRunning = false;
        }
    }

    function __perfDump() {
        console.group('[perf-watchdog] ' + new Date().toLocaleTimeString());
        console.log('Heavy ops (' + __heavyLog.length + '):');
        __heavyLog.forEach(e => console.log('  ' + e.op + ': ' + e.ms + 'ms (' + e.path + ')'));
        if (!__watchdogWorker) {
            console.log('Frame blocks: worker unavailable');
            console.groupEnd();
            return;
        }
        __watchdogWorker.addEventListener('message', function handler(e) {
            const d = e.data;
            if (d.type !== 'dump') return;
            __watchdogWorker.removeEventListener('message', handler);
            console.log('Frame blocks (' + d.blocks.length + '):');
            d.blocks.forEach(b => console.log('  ' + b.ms + 'ms @ ' + b.op + ' (' + b.path + ')' + (b.ip ? ' [FROZE]' : '')));
            if (d.ip) console.warn('IN-PROGRESS BLOCK: ' + d.ip.op + ' @ ' + d.ip.path + ' (started ' + new Date(d.ip.start).toLocaleTimeString() + ')');
            console.groupEnd();
        });
        __watchdogWorker.postMessage({type:'dump'});
    }

    function __perfCrashRecovery() {
        if (!window.indexedDB) return;
        const req = indexedDB.open('logistics_perf', 1);
        req.onupgradeneeded = function(e) { e.target.result.createObjectStore('blocks', {autoIncrement: true}); };
        req.onsuccess = function(e) {
            const db = e.target.result;
            try {
                const tx = db.transaction('blocks', 'readwrite');
                const store = tx.objectStore('blocks');
                const getAll = store.getAll();
                getAll.onsuccess = function() {
                    const recovered = getAll.result || [];
                    if (recovered.length) {
                        console.group('[perf] CRASH RECOVERY — ' + recovered.length + ' frame blocks from previous session:');
                        recovered.forEach(b => console.log('  ' + b.ms + 'ms @ ' + b.op + ' (' + b.path + ')' + (b.ip ? ' [FROZE]' : '')));
                        console.groupEnd();
                        store.clear();
                    }
                    db.close();
                };
                getAll.onerror = function() { db.close(); };
            } catch (err) { db.close(); }
        };
        req.onerror = function() {};
    }

    function qolGoToNav() {
        __perfMark('nav_return_click');
        try {
            top.frames.main.location.href = '//app/main?nav=1';
        } catch (err) {
            top.location.href = '//app/main?nav=1';
        }
    }

    function qolDescribeNextStep() {
        const path = window.location.pathname;
        const activeData = GM_getValue('logistics_route_v5', { steps: [] });
        const steps = activeData.steps || [];

        if (path === '//app/main' || path.endsWith('//app/main')) {
            if (steps.length === 0) return '\u2713 Route complete';
            const target = steps[0];
            const coordsEl = document.getElementById('coords');
            const current = coordsEl ? coordsEl.innerText.trim() : '';
            if (normalizeCoords(current) !== normalizeCoords(target.location)) {
                return `\u2708 Fly to ${target.location} ${target.name}`;
            }
            return `\u2693 Open trade menu at ${target.location}`;
        }

        if (path.includes('/app/trade') || path.includes('/app/manage')) {
            const inputs = Array.from(document.querySelectorAll(allTradeInputSelector()));
            const hasSell = inputs.some(i => classifyTradeInput(i) === 'sell' && parseInt(i.value, 10) > 0);
            const hasBuy = inputs.some(i => classifyTradeInput(i) === 'buy' && parseInt(i.value, 10) > 0);
            if (hasSell) return '\ud83d\udce4 Trade: drop off cargo';
            if (hasBuy) return '\ud83d\udce5 Trade: pick up cargo';
            return '\u2713 Close trade menu';
        }

        return '\u2014 No action';
    }

    function qolNextStep() {
        __perfMark('qol_next');
        const path = window.location.pathname;

        if (path === '//app/main' || path.endsWith('//app/main')) {
            const activeData = GM_getValue('logistics_route_v5', { steps: [] });
            const steps = activeData.steps || [];
            if (steps.length === 0) { alert('No active route step. Run Sync & Sim first.'); return; }

            const target = steps[0];
            const coordsEl = document.getElementById('coords');
            if (!coordsEl) { alert('Cannot read current coords from nav screen.'); return; }
            const current = coordsEl.innerText.trim();

            if (normalizeCoords(current) !== normalizeCoords(target.location)) {
                if (typeof flyHereToStep === 'function') {
                    const statusEl = document.getElementById('qol-status');
                    const btnEl = document.getElementById('qol-next-btn');
                    if (btnEl) { btnEl.disabled = true; btnEl.style.opacity = '0.5'; }
                    if (statusEl) statusEl.innerText = '\u2708 Flying...';
                    flyHereToStep((arrived) => {
                        if (btnEl) { btnEl.disabled = false; btnEl.style.opacity = '1'; }
                        if (statusEl) statusEl.innerText = qolDescribeNextStep();
                    });
                } else {
                    alert('Fly function unavailable.');
                }
                return;
            }

            // Arrived — open the trade screen by clicking the trade link on
            // the nav page.  The nav page shows a 5x5 grid of
            // surrounding tiles, each with its own building/trade links, so
            // a blanket querySelector can match a neighbouring tile's
            // /app/trade link instead of the player's own
            // /app/manage link.  Prefer management links first
            // (owner inventory screen), and scope the initial search to the
            // commands panel (current-tile actions) before falling back to
            // the full nav grid.
            const cmdPanel = document.getElementById('commands') || document.body;
            let tradeLink = cmdPanel.querySelector('a[href*="/app/manage"]');
            if (!tradeLink) tradeLink = document.querySelector('a[href*="/app/manage"]');
            if (!tradeLink) tradeLink = cmdPanel.querySelector('a[href*="/app/trade"]');
            if (!tradeLink) tradeLink = cmdPanel.querySelector('a[href*="/app/trade2"]');
            if (!tradeLink) tradeLink = cmdPanel.querySelector('a[href*="/app/trade3"]');
            if (!tradeLink) tradeLink = document.querySelector('a[href*="/app/trade"], a[href*="/app/trade2"], a[href*="/app/trade3"]');
            if (tradeLink) {
                GM_setValue('logistics_trade_loc', normalizeCoords(current));
                __perfMark('trade_get_click');
                tradeLink.click();
            } else {
                alert('Arrived at ' + target.location + ' but no trade link found on the nav screen. Open the trade screen manually, then press Next Step again.');
            }
            return;
        }

        if (path.includes('/app/trade') || path.includes('/app/manage')) {
            const inputs = Array.from(document.querySelectorAll(allTradeInputSelector()));
            const hasSell = inputs.some(i => classifyTradeInput(i) === 'sell' && parseInt(i.value, 10) > 0);
            const hasBuy = inputs.some(i => classifyTradeInput(i) === 'buy' && parseInt(i.value, 10) > 0);

            function submitTrade() {
                const btn = document.querySelector('input[type="submit"][value*="Transfer"], input[type="submit"][value*="Trade"], input[name="trade"]');
                if (btn) btn.click();
                else if (document.forms.length > 0) document.forms[document.forms.length - 1].submit();
            }

            if (hasSell || hasBuy) {
                // Submit buys and sells together (same as the manual Transfer button).
                // If the server rejects the simultaneous dual-trade, the on-screen
                // "Execute ONLY Dropoffs / Pickups" split buttons handle it as a fallback.
                __perfMark('trade_post_click');
                submitTrade();
                return;
            }
            // Nothing left to trade here — close the trade menu and return to nav.
            GM_deleteValue('logistics_trade_loc');
            qolGoToNav();
            return;
        }
    }

    function bindQolHotkey() {
        if (window.__qolHotkeyBound) return;
        window.__qolHotkeyBound = true;
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Escape') {
                if (GM_getValue('logistics_auto_step', false)) {
                    e.preventDefault();
                    stopAutoStep();
                }
                return;
            }
            if (e.key !== 't' && e.key !== 'T') return;
            const tag = (e.target.tagName || '').toUpperCase();
            if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
            if (e.ctrlKey || e.altKey || e.metaKey) return;
            const btn = document.getElementById('qol-next-btn');
            if (btn && !btn.disabled) { e.preventDefault(); btn.click(); }
        });
    }

    // >> Auto-step (spam "t") support
    function autoStepTick() {
        if (!GM_getValue('logistics_auto_step', false)) return;
        const activeData = GM_getValue('logistics_route_v5', { steps: [] });
        if (!(activeData.steps || []).length) {
            GM_setValue('logistics_auto_step', false);
            const autoBtn = document.getElementById('qol-auto-btn');
            const stopBtn = document.getElementById('qol-stop-btn');
            if (autoBtn) { autoBtn.disabled = false; autoBtn.style.opacity = '1'; }
            if (stopBtn) { stopBtn.disabled = true; stopBtn.style.opacity = '0.5'; }
            const statusEl = document.getElementById('qol-status');
            if (statusEl) statusEl.innerText = qolDescribeNextStep();
            injectSkippedPanels();
            __perfReport();
            return;
        }
        const btn = document.getElementById('qol-next-btn');
        if (!btn) { GM_setValue('logistics_auto_step', false); return; }
        if (btn.disabled) { setTimeout(autoStepTick, 150); return; }
        btn.click();
        btn.disabled = true;
        btn.style.opacity = '0.5';
        setTimeout(autoStepTick, 100);
    }

    function startAutoStep() {
        GM_setValue('logistics_auto_step', true);
        const autoBtn = document.getElementById('qol-auto-btn');
        const stopBtn = document.getElementById('qol-stop-btn');
        if (autoBtn) { autoBtn.disabled = true; autoBtn.style.opacity = '0.5'; }
        if (stopBtn) { stopBtn.disabled = false; stopBtn.style.opacity = '1'; }
        const statusEl = document.getElementById('qol-status');
        if (statusEl) statusEl.innerText = '\u23a9 Auto-stepping...';
        autoStepTick();
    }

    function stopAutoStep() {
        GM_setValue('logistics_auto_step', false);
        const autoBtn = document.getElementById('qol-auto-btn');
        const stopBtn = document.getElementById('qol-stop-btn');
        if (autoBtn) { autoBtn.disabled = false; autoBtn.style.opacity = '1'; }
        if (stopBtn) { stopBtn.disabled = true; stopBtn.style.opacity = '0.5'; }
        const statusEl = document.getElementById('qol-status');
        if (statusEl) statusEl.innerText = qolDescribeNextStep();
        injectSkippedPanels();
        __perfReport();
    }

    function checkStuckStop(stepLocation) {
        if (!stepLocation) return false;
        const last = GM_getValue('logistics_last_trade_step_loc', '');
        let count = GM_getValue('logistics_stuck_count', 0);
        if (normalizeCoords(last) === normalizeCoords(stepLocation)) {
            count += 1;
        } else {
            count = 1;
            GM_setValue('logistics_last_trade_step_loc', stepLocation);
        }
        GM_setValue('logistics_stuck_count', count);
        if (count >= 3) {
            stopAutoStep();
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed; top:0; left:0; width:100%; background:#660000; color:#ffff00; text-align:center; padding:12px; z-index:999999; font-weight:bold; font-size:14px; border-bottom:3px solid #ff0000; box-shadow:0px 4px 10px rgba(0,0,0,0.8);';
            overlay.innerText = '⚠ AUTO-RUN STOPPED: Stuck at ' + stepLocation + ' (trade stop not completing after ' + count + ' attempts). Building may be full or trade rejected. Check and resume manually.';
            document.body.appendChild(overlay);
            GM_deleteValue('logistics_last_trade_step_loc');
            GM_deleteValue('logistics_stuck_count');
            return true;
        }
        return false;
    }

    function injectSkippedPanels() {
        const path = window.location.pathname;
        if (path !== '//app/main' && !path.endsWith('//app/main')) return;
        if (!document.getElementById('nav-btn-fly-here')) {
            try { injectNavHUD(); }
            catch (e) { console.error('[logistics-nav] HUD inject failed:', e); }
        }
        if (!document.getElementById('logistics-flyhere-panel')) {
            try { injectFlyHerePanel(); }
            catch (e) { console.error('[logistics-flyhere] panel inject failed:', e); }
        }
        if (!document.getElementById('logistics-exports-panel')) {
            try { injectExportsCalculator(); }
            catch (e) { console.error('[logistics-exports] panel inject failed:', e); }
        }
        if (!document.getElementById('logistics-tracker-panel')) {
            try { injectTrackerPanel(); }
            catch (e) { console.error('[logistics-tracker] panel inject failed:', e); }
        }
    }

    function bindQolAutoButtons() {
        const autoBtn = document.getElementById('qol-auto-btn');
        const stopBtn = document.getElementById('qol-stop-btn');
        if (autoBtn) autoBtn.addEventListener('click', startAutoStep);
        if (stopBtn) stopBtn.addEventListener('click', stopAutoStep);
    }

    // Resume auto-stepping after a page navigation caused by a previous step.
    function autoStepResume() {
        if (!GM_getValue('logistics_auto_step', false)) return;
        const btn = document.getElementById('qol-next-btn');
        if (!btn) { GM_setValue('logistics_auto_step', false); return; }
        btn.disabled = false;
        btn.style.opacity = '1';
        const autoBtn = document.getElementById('qol-auto-btn');
        const stopBtn = document.getElementById('qol-stop-btn');
        if (autoBtn) { autoBtn.disabled = true; autoBtn.style.opacity = '0.5'; }
        if (stopBtn) { stopBtn.disabled = false; stopBtn.style.opacity = '1'; }
        const statusEl = document.getElementById('qol-status');
        if (statusEl) statusEl.innerText = '\u23a9 Auto-stepping...';
        setTimeout(autoStepTick, 80);
    }

    function injectNavHUD() {
        const activeData = GM_getValue('logistics_route_v5', { steps: [] });
        const safeSteps = activeData.steps || [];
        if (safeSteps.length === 0) return;

        const nextTarget = safeSteps[0];

        let drops = Object.entries(nextTarget.dropoffs || {}).map(([name, data]) => `${data.amount} ${name}`).join(', ');
        let picks = Object.entries(nextTarget.pickups || {}).map(([name, data]) => `${data.amount} ${name}`).join(', ');

        let statusText = `Next Stop: <span style="color:#fff;">${nextTarget.location} ${nextTarget.name}</span>`;
        if (drops) statusText += ` &nbsp;|&nbsp; <span style="color:#ff5555;">⬇ Drop: ${drops}</span>`;
        if (picks) statusText += ` &nbsp;|&nbsp; <span style="color:#55ff55;">⬆ Pick: ${picks}</span>`;

        try {
            if (normalizeCoords(document.getElementById('coords').innerText) === normalizeCoords(nextTarget.location)) {
                statusText = `<span style="color:#fff;">ARRIVED AT: ${nextTarget.location} ${nextTarget.name}</span> &nbsp;|&nbsp; Dock to execute trade.`;
            }
        } catch (e) {}

        const hud = document.createElement('div');
        hud.style.cssText = `background: #000022; color: #0f0; text-align: center; padding: 6px; border-bottom: 1px solid #444; font-weight: bold; font-family: Verdana, sans-serif; font-size: 13px;`;
        hud.innerHTML = `
            <div>${statusText}</div>
            <div style="margin-top: 4px;">
                <button id="nav-btn-fly-here" style="cursor: pointer; padding: 3px 12px; background: #003355; color: #88ccff; border: 1px solid #0088ff; font-weight: bold; font-size: 12px;">✈ Fly Here</button>
            </div>
        `;
        document.body.insertBefore(hud, document.body.firstChild);

        document.getElementById('nav-btn-fly-here').addEventListener('click', flyHereToStep);
    }

    // --- 12. Exports Calculator ---
    //
    // Ranks export routes for the goods stashed in the player's personal
    // Transit Hub (config_export_items). For every tracked station /
    // station / TH that BUYS one of those commodities (sellToObjPrice > 0) and
    // still has room, it computes a credit-to-AP ratio and lists the routes
    // from best to worst.
    //
    // Buy-side cost basis = "the default price I bought them for". This is the
    // cheapest buyFromObjPrice seen across tracked producer buildings (e.g.
    // robot factories for Robots). A manual override is available via
    // config_export_buy_price.
    //
    // Distance model (one-way AP from the TH to the destination):
    //   * Same sector as the TH  -> exact Dijkstra (getSectorAllDistances).
    //     Cross-sector AP stays null (?) in the panel display, but clicking
    //     a cross-sector destination name now auto-flies there via wormhole
    //     routing (getCrossSectorRoute in the equip_f module).
    //
    // Packaging model:
    //   * Normal cargo cap = maxCargo (200). For any destination whose one-way
    //     AP (D) exceeds the packing overhead (PACK_AP = 400), the player may
    //     spend 400 AP to enable packaging, doubling cargo capacity for that
    //     one trip (up to PACK_CAP = maxCargo*2 = 400). Packed apCost = D+400.
    //   * Break-even vs two unpacked 200-batches (2*D): D+400 = 2*D -> D = 400.
    //     Packing is a strict win only when D > 400, and only when the buyer
    //     has room for more than one unpacked batch (> 200 units). If the buyer
    //     has <= 200 room, the 400 AP overhead would be wasted carrying <= 200
    //     units that fit unpacked in a single trip, so packing is NOT applied.
    //   * Packed routes are flagged "(packaging)" in the panel so the player
    //     knows the doubled capacity + AP overhead is in effect.
    //   * Note: packaging draws from a finite stock of 400 packages; this
    //     calculator flags per-route packability but does not deplete a global
    //     packaging inventory across multiple ranked routes.
    //
    // Ratio = net profit / apCost  (credits earned per AP, after subtracting
    // the buy cost). Falls back to revenue/apCost if no buy price is known.
    //
    // (Internal sub-comments below intentionally avoid the "// --- X ---"
    // marker shape so split-trading.js does not fragment this section.)

    function buildExportNameToResIdMap(store) {
        const map = {};
        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities) continue;
            for (const rid in e.commodities) {
                const c = e.commodities[rid];
                if (c && c.name) map[c.name.toLowerCase()] = rid;
            }
        }
        return map;
    }

    // Recompute real sector + local coords from userloc (same method the
    // tracker panel uses for display).  Stored e.sector / e.coords can be
    // wrong (e.g. hostname fallback "seal_a" instead of real sector name).
    function realSectorAndCoords(e) {
        const sector = getSectorFromTileId(e.userloc);
        if (!sector) return { sector: e.sector || null, coords: null };
        const c = getLocalCoordsFromTileId(e.userloc, sector);
        return { sector: sector, coords: c };
    }

    function findExportToEntry(store, toCoords) {
        if (!toCoords) return null;
        // Match by recomputed coords (reliable), not stored e.coords.
        let best = null;
        for (const k in store) {
            const e = store[k];
            if (!e || e.userloc == null) continue;
            const rc = realSectorAndCoords(e);
            if (!rc.coords) continue;
            if (rc.coords.x === toCoords.x && rc.coords.y === toCoords.y) {
                if (!best) best = e;
                if (e.playerOwned || e.ownBase) { best = e; break; }
            }
        }
        return best;
    }

    // Cheapest buyFromObjPrice across tracked non-player-owned producers.
    function resolveExportBuyPrice(store, resId, override) {
        if (override != null && !isNaN(override) && override > 0) {
            return { price: override, source: 'manual override' };
        }
        let min = Infinity, src = null;
        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities || e.playerOwned) continue;
            const c = e.commodities[resId];
            if (c && c.buyFromObjPrice > 0 && c.buyFromObjPrice < min) {
                min = c.buyFromObjPrice;
                src = e.name || ('loc ' + e.userloc);
            }
        }
        if (min === Infinity) return { price: null, source: null };
        return { price: min, source: src };
    }

    // Captures the live stock of the player's personal Transit Hub by
    // parsing the /app/manage DOM. The TH has no trade prices and
    // is never captured by captureTradeScreen() into trade_tracker_v1, so the
    // exports calculator keeps its own isolated record under `to_actual_stock_v1`
    // (keyed by lowercased commodity name). Only this panel reads it; the route
    // simulator's `toInventory` and the trade-tracker store are left untouched.
    function capturePersonalToStock() {
        if (!isTradingOutpostPage()) return null;
        const stock = {};
        const inputs = document.querySelectorAll(allTradeInputSelector());
        inputs.forEach(input => {
            if (classifyTradeInput(input) !== 'buy') return; // building-side rows only
            const row = input.closest('tr');
            if (!row) return;
            const name = readRowCommodityName(row);
            if (!name) return;
            let amt = NaN;
            const useMaxLink = row.querySelector('a[href*="useMax"]');
            if (useMaxLink) {
                const s = useMaxLink.textContent.replace(/[^\d]/g, '');
                if (s !== '') amt = parseInt(s, 10);
            }
            if (isNaN(amt)) {
                const cells = Array.from(row.querySelectorAll('td'));
                if (cells.length > 2) {
                    const s = cells[2].textContent.replace(/[^\d]/g, '');
                    if (s !== '') amt = parseInt(s, 10);
                }
            }
            if (!isNaN(amt)) stock[name.toLowerCase()] = amt;
        });
        if (Object.keys(stock).length === 0) return null;
        const entry = {
            stock: stock,
            capturedAt: Date.now(),
            userloc: readPageVar('userloc')
        };
        GM_setValue('to_actual_stock_v1', entry);
        console.log('[logistics-exports] captured personal TH stock:', Object.keys(stock).length, 'commodities');
        return entry;
    }

    // Returns the TH stock map to use for the exports panel. Prefers the
    // captured actual stock (from the last /app/manage visit);
    // falls back to the route simulator's projected stash only when the TH has
    // never been visited, so the panel isn't blank on first use.
    function getPersonalToStockMap() {
        const entry = GM_getValue('to_actual_stock_v1', null);
        if (entry && entry.stock && typeof entry.stock === 'object') return entry.stock;
        const routeState = GM_getValue('logistics_route_v5', { steps: [], toInventory: {} });
        return (routeState && routeState.toInventory) ? routeState.toInventory : {};
    }

    function computeExportRoutes() {
        __setOp('computeExportRoutes');
        const toCoordsRaw = GM_getValue('config_to_coords', '');
        const toCoords = toCoordsRaw ? parseCoords(toCoordsRaw) : null;
        const exportsRaw = GM_getValue('config_export_items', '');
        const exportItems = exportsRaw.split(',').map(s => s.trim()).filter(Boolean);
        const buyOverride = parseInt(GM_getValue('config_export_buy_price', ''), 10);
        const maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;

        if (!toCoords || exportItems.length === 0) {
            return { error: 'Set TH Coords and Exports in the Logistics Sim panel first.' };
        }

        parseStaticMap(true);
        const store = getTrackerStore();
        if (Object.keys(store).length === 0) {
            return { error: 'No tracked locations yet. Open building/station/station trade screens to capture them.' };
        }
        const _rcCache = new Map();
        const _rcOf = (e) => {
            const hit = _rcCache.get(e.userloc);
            if (hit !== undefined) return hit;
            const rc = realSectorAndCoords(e);
            _rcCache.set(e.userloc, rc);
            return rc;
        };

        const nameToResId = buildExportNameToResIdMap(store);
        const toEntry = findExportToEntry(store, toCoords);

        // Personal Transit Hubs are entered via /app/manage,
        // which has no trade prices and is never captured by captureTradeScreen()
        // into the trade-tracker store. Their actual stashed stock is captured
        // into the isolated `to_actual_stock_v1` key whenever the player visits
        // the TH page (see capturePersonalToStock). Use it as the TH stock
        // source so this panel reflects ground truth, not just the simulator's
        // projection.
        const toStash = getPersonalToStockMap();

        // TH sector: from the tracked TH entry's tile ID, or from the
        // player's current position (/app/main has userloc).
        const toSector = toEntry
            ? getSectorFromTileId(toEntry.userloc)
            : getSectorFromTileId(trackerGetPlayerTileId());

        // One Dijkstra run from the TH covers every same-sector destination.
        let toDijkstra = null;
        let usedFallback = false;
        if (toSector) {
            try {
                toDijkstra = getSectorAllDistances(toSector, toCoords.x, toCoords.y);
            } catch (e) { toDijkstra = null; }
            if (!toDijkstra) usedFallback = true;
        }

        const routes = [];
        const itemInfo = {};

        for (const itemName of exportItems) {
            const resId = nameToResId[itemName.toLowerCase()];
            if (!resId) {
                itemInfo[itemName] = { note: 'not tracked \u2014 no trade screen lists this commodity' };
                continue;
            }

            const buy = resolveExportBuyPrice(store, resId, buyOverride);
            const buyPrice = buy.price;

            let toStock = null;
            if (toEntry && toEntry.commodities && toEntry.commodities[resId]) {
                toStock = toEntry.commodities[resId].stock;
            } else {
                // Personal TO: not in the trade tracker. Read the captured
                // actual stock instead. Missing key = not stashed = 0 (skip).
                toStock = toStash[itemName.toLowerCase()] || 0;
            }
            itemInfo[itemName] = {
                resId: resId,
                buyPrice: buyPrice,
                buySource: buy.source,
                toStock: toStock
            };

            for (const k in store) {
                const e = store[k];
                if (!e || !e.commodities) continue;
                if (toEntry && e.userloc === toEntry.userloc) continue;

                const c = e.commodities[resId];
                if (!c || c.sellToObjPrice <= 0) continue;

                // Real sector + coords from tile ID (not stored e.sector/e.coords).
                const rc = _rcOf(e);
                if (!rc.coords) continue;
                const eSector = rc.sector;
                const eCoords = rc.coords;

                const sameSector = !!(eSector && toSector && eSector === toSector);

                // AP from TO: exact same-sector Dijkstra, or wormhole-aware
                // HPA* routing for cross-sector buyers (same equip_f the
                // Opportunities tab uses). Unknown/unreachable → null → "?"
                // display (no estimates, per AGENTS.md hard-fail policy).
                let D = null;
                if (sameSector && toDijkstra) {
                    const key = eCoords.x + ',' + eCoords.y;
                    D = (toDijkstra[key] !== undefined) ? toDijkstra[key] : null;
                } else if (!sameSector && eSector && toSector) {
                    try {
                        D = getCrossSectorAPFast(toCoords, toSector, eCoords, eSector, null, null);
                    } catch (e) { D = null; }
                }

                // Packaging: spend PACK_AP (400) to double cargo capacity for one
                // trip (up to PACK_CAP = maxCargo*2). Breaks even vs two unpacked
                // 200-batches at D = PACK_AP and saves more the farther D is past
                // that. Only worthwhile when (a) D is known and exceeds the
                // break-even distance, AND (b) the buyer has room for more than a
                // single unpacked batch — otherwise the 400 AP overhead is wasted
                // carrying <= 200 units that would have fit unpacked in one trip.
                const PACK_AP = 400;
                const PACK_CAP = maxCargo * 2;
                let usePacking = false;

                const unpackedDesired = Math.min(maxCargo, toStock == null ? maxCargo : toStock);
                const unpackedProj = trackerProjectSell(e, resId, unpackedDesired);

                if (D != null && D > PACK_AP) {
                    const packDesired = Math.min(PACK_CAP, toStock == null ? PACK_CAP : toStock);
                    const packProj = trackerProjectSell(e, resId, packDesired);
                    if (packProj && packProj.quantity > maxCargo) {
                        usePacking = true;
                    }
                }

                const proj = usePacking
                    ? trackerProjectSell(e, resId, Math.min(PACK_CAP, toStock == null ? PACK_CAP : toStock))
                    : unpackedProj;
                if (!proj || proj.quantity <= 0) continue;

                const units = proj.quantity;
                const revenue = proj.totalRevenue;
                const sellPerUnit = proj.perUnitAvg;
                const profit = (buyPrice != null) ? (revenue - buyPrice * units) : null;

                const apCost = (D != null) ? (D + (usePacking ? PACK_AP : 0)) : null;
                const credit = (profit != null) ? profit : revenue;
                const ratio = (apCost != null && apCost > 0) ? credit / apCost : null;

                routes.push({
                    item: itemName,
                    dest: e,
                    sector: eSector,
                    coords: eCoords,
                    sameSector: sameSector,
                    packed: usePacking,
                    units: units,
                    buyPrice: buyPrice,
                    sellPerUnit: sellPerUnit,
                    revenue: revenue,
                    profit: profit,
                    credit: credit,
                    apCost: apCost,
                    ratio: ratio
                });
            }
        }

        routes.sort((a, b) => {
            if (a.ratio != null && b.ratio != null) return b.ratio - a.ratio;
            if (a.ratio != null) return -1;
            if (b.ratio != null) return 1;
            return (b.credit || 0) - (a.credit || 0);
        });

        return {
            routes: routes,
            toEntry: toEntry,
            toSector: toSector,
            toCoords: toCoords,
            itemInfo: itemInfo,
            usedFallback: usedFallback
        };
    }

    // >> Custom export: single-item, flexible-origin route planner
    //
    // Like computeExportRoutes but for one user-specified item+quantity from a
    // flexible origin (current position or chosen coords+sector). Same route
    // shape, same packaging model, same helpers. Buy price auto-detected via
    // resolveExportBuyPrice (shared cfgBar override).
    function computeCustomExportRoutes(opts) {
        const maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;

        // --- Resolve origin ---
        let originCoords, originSector;
        if (opts.originMode === 'current') {
            const tileId = trackerGetPlayerTileId();
            if (tileId == null) {
                return { error: 'Current position unavailable (no userloc on this page). Use Coords mode or switch to a nav/main page.' };
            }
            originSector = getSectorFromTileId(tileId);
            if (!originSector) return { error: 'Could not resolve sector for current tile ' + tileId + '.' };
            originCoords = getLocalCoordsFromTileId(tileId, originSector);
            if (!originCoords) return { error: 'Could not resolve local coords for current tile.' };
        } else {
            if (!opts.coordsStr || !/\d+,\d+/.test(opts.coordsStr)) {
                return { error: 'Enter origin coords as x,y (e.g. 12,5).' };
            }
            originCoords = parseCoords(opts.coordsStr);
            const resolvedSector = _resolveSectorName(opts.sectorStr);
            if (!resolvedSector) {
                return { error: 'Unknown sector "' + (opts.sectorStr || '') + '". Check the sector name spelling.' };
            }
            originSector = resolvedSector;
        }

        // --- Resolve item + store ---
        parseStaticMap(true);
        const store = getTrackerStore();
        if (Object.keys(store).length === 0) {
            return { error: 'No tracked locations yet. Open building/station/station trade screens to capture them.' };
        }
        const nameToResId = buildExportNameToResIdMap(store);
        const itemName = (opts.itemName || '').trim();
        const resId = nameToResId[itemName.toLowerCase()];
        if (!resId) {
            return { error: 'Item "' + itemName + '" is not tracked. Open a trade screen that lists this commodity.' };
        }
        const qty = parseInt(opts.qty, 10);
        if (!qty || qty <= 0) {
            return { error: 'Enter a positive quantity to transport.' };
        }

        const buyOverride = opts.buyOverride != null && !isNaN(opts.buyOverride) && opts.buyOverride > 0 ? opts.buyOverride : null;
        const buy = resolveExportBuyPrice(store, resId, buyOverride);
        const buyPrice = buy.price;

        // --- One Dijkstra from origin covers all same-sector destinations ---
        let originDijkstra = null;
        let usedFallback = false;
        try { originDijkstra = getSectorAllDistances(originSector, originCoords.x, originCoords.y); }
        catch (e) { originDijkstra = null; }
        if (!originDijkstra) usedFallback = true;

        const routes = [];
        const PACK_AP = 400;
        const PACK_CAP = maxCargo * 2;

        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities) continue;
            const c = e.commodities[resId];
            if (!c || c.sellToObjPrice <= 0) continue;

            const rc = realSectorAndCoords(e);
            if (!rc.coords) continue;
            const eSector = rc.sector;
            const eCoords = rc.coords;

            const sameSector = !!(eSector && eSector === originSector);

            // AP: same-sector Dijkstra, cross-sector HPA* (no estimates — null → '?')
            let D = null;
            if (sameSector && originDijkstra) {
                const key = eCoords.x + ',' + eCoords.y;
                D = (originDijkstra[key] !== undefined) ? originDijkstra[key] : null;
            } else if (!sameSector && eSector) {
                try { D = getCrossSectorAPFast(originCoords, originSector, eCoords, eSector, null, null); }
                catch (e2) { D = null; }
            }

            // Packaging model (same as computeExportRoutes)
            let usePacking = false;
            const unpackedDesired = Math.min(maxCargo, qty);
            const unpackedProj = trackerProjectSell(e, resId, unpackedDesired);
            if (D != null && D > PACK_AP) {
                const packDesired = Math.min(PACK_CAP, qty);
                const packProj = trackerProjectSell(e, resId, packDesired);
                if (packProj && packProj.quantity > maxCargo) usePacking = true;
            }
            const proj = usePacking
                ? trackerProjectSell(e, resId, Math.min(PACK_CAP, qty))
                : unpackedProj;
            if (!proj || proj.quantity <= 0) continue;

            const units = proj.quantity;
            const revenue = proj.totalRevenue;
            const sellPerUnit = proj.perUnitAvg;
            const profit = (buyPrice != null) ? (revenue - buyPrice * units) : null;
            const apCost = (D != null) ? (D + (usePacking ? PACK_AP : 0)) : null;
            const credit = (profit != null) ? profit : revenue;
            const ratio = (apCost != null && apCost > 0) ? credit / apCost : null;

            routes.push({
                item: itemName, dest: e, sector: eSector, coords: eCoords,
                sameSector: sameSector, packed: usePacking, units: units,
                buyPrice: buyPrice, sellPerUnit: sellPerUnit, revenue: revenue,
                profit: profit, credit: credit, apCost: apCost, ratio: ratio
            });
        }

        routes.sort((a, b) => {
            if (a.ratio != null && b.ratio != null) return b.ratio - a.ratio;
            if (a.ratio != null) return -1;
            if (b.ratio != null) return 1;
            return (b.credit || 0) - (a.credit || 0);
        });

        return {
            routes: routes,
            originSector: originSector,
            originCoords: originCoords,
            itemName: itemName,
            resId: resId,
            qty: qty,
            buyPrice: buyPrice,
            buySource: buy.source,
            usedFallback: usedFallback
        };
    }

    // cycle (Res_A/Res_B/Res_C) cycle calculator.
    //
    // Cycle: buy res_a+res_b at the hub station (123:84 ratio of max cargo),
    // travel to a station in the same sector, sell res_a+res_b and buy res_c,
    // travel back to the hub, sell res_c. One complete round-trip cycle.
    //
    // Profit = (sell Res_A/Res_B to station + sell res_c to hub)
    //        - (buy Res_A/Res_B from hub + buy res_c from station)
    // AP     = round-trip terrain travel + TRADE_AP (2 combined trade actions)
    // cr/AP  = profit / AP
    //
    // Hub station and station prices come from the trade tracker store
    // (curve-aware for planets/stations via trackerProjectBuy/Sell).
    // Only stations in the SAME sector as the hub are listed (the local
    // equip_f cannot route cross-sector).
    function computecycleRoutes() {
        const hubCoordsRaw = GM_getValue('config_hub_coords', '');
        const hubCoords = hubCoordsRaw ? parseCoords(hubCoordsRaw) : null;
        const maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;

        if (!hubCoords) {
            return { error: 'Set Hub Coords in the Logistics Sim panel first.' };
        }

        parseStaticMap(true);
        const store = getTrackerStore();
        if (Object.keys(store).length === 0) {
            return { error: 'No tracked locations yet. Open station/station trade screens to capture them.' };
        }

        const nameToResId = buildExportNameToResIdMap(store);
        const resAId = nameToResId['res_a'];
        const resBId = nameToResId['res_b'];
        const resCId = nameToResId['res_c'];

        if (!resAId || !resBId || !resCId) {
            return { error: 'Res_A/Res_B/Res_C not found in tracked data. Open the hub station and station trade screens to capture them.' };
        }

        const hubEntry = findExportToEntry(store, hubCoords);
        if (!hubEntry) {
            return { error: 'Hub station not tracked at [' + hubCoords.x + ',' + hubCoords.y + ']. Open its trade screen to capture prices.' };
        }

        if (!hubEntry.commodities[resAId] || !hubEntry.commodities[resBId] || !hubEntry.commodities[resCId]) {
            return { error: 'Hub station missing res_a/res_b/res_c data. Re-open its trade screen.' };
        }

        const hubSector = getSectorFromTileId(hubEntry.userloc);

        // One Dijkstra run from the hub covers every same-sector station.
        let hubDijkstra = null;
        let usedFallback = false;
        if (hubSector) {
            try {
                hubDijkstra = getSectorAllDistances(hubSector, hubCoords.x, hubCoords.y);
            } catch (e) { hubDijkstra = null; }
            if (!hubDijkstra) usedFallback = true;
        }

        // Res_A/Res_B cargo split: 123:84 ratio (user's hullspace tuning).
        const RES_A_RATIO = 123, RES_B_RATIO = 84, RATIO_SUM = RES_A_RATIO + RES_B_RATIO;
        const desiredResA = Math.floor(maxCargo * RES_A_RATIO / RATIO_SUM);
        const desiredResB = Math.floor(maxCargo * RES_B_RATIO / RATIO_SUM);

        // Trade AP: 2 combined trade actions (hub: sell E + buy Res_A/Res_B in one
        // form; station: sell Res_A/Res_B + buy E in one form). Each costs 5 AP.
        const TRADE_AP = 10;

        const routes = [];
        // Diagnostic: track why each tracked station was rejected so the
        // empty-state message can explain itself instead of being a dead end.
        // The exports tab lists cross-sector buyers too (with HPA* AP); this
        // cycle tab also includes cross-sector stations (routed via HPA*), so
        // the only stations that land in crossSector here are truly
        // unresolved tiles (no coords extractable from the tile ID).
        const stats = {
            totalStations: 0,
            notStation: 0,
            isHub: 0,
            missingCommodity: [],
            noPrice: [],
            crossSector: [],
            noStockRoom: [],
            qualified: 0
        };

        for (const k in store) {
            const st = store[k];
            if (!st || !st.commodities) continue;
            if (st.type !== 'station') { stats.notStation++; continue; }
            stats.totalStations++;
            if (st.userloc === hubEntry.userloc) { stats.isHub++; continue; }

            // Station must buy res_a+res_b and sell res_c.
            const stResA = st.commodities[resAId];
            const stResB = st.commodities[resBId];
            const stResC = st.commodities[resCId];
            if (!stResA || !stResB || !stResC) {
                const missing = [];
                if (!stResA) missing.push('res_a');
                if (!stResB) missing.push('res_b');
                if (!stResC) missing.push('res_c');
                stats.missingCommodity.push((st.name || '?') + ' (missing ' + missing.join('+') + ')');
                continue;
            }
            if (stResA.sellToObjPrice <= 0 || stResB.sellToObjPrice <= 0 || stResC.buyFromObjPrice <= 0) {
                stats.noPrice.push((st.name || '?') +
                    ' [F sell=' + stResA.sellToObjPrice +
                    ', W sell=' + stResB.sellToObjPrice +
                    ', E buy=' + stResC.buyFromObjPrice + ']');
                continue;
            }

            const rc = realSectorAndCoords(st);
            if (!rc.coords) {
                stats.crossSector.push((st.name || '?') + ' (unresolved tile ' + st.userloc + ')');
                continue;
            }
            const stSector = rc.sector;
            const stationCoords = rc.coords;

            // Cross-sector stations are routed via HPA* (same equip_f as
            // the exports tab and Opportunities tab). Unresolved sector/coords
            // still rejected above; unreachable targets → null AP → "?".
            const sameSectorcycle = !!(stSector && hubSector && stSector === hubSector);

            // Actual res_a qty = min(hub can sell, station can buy).
            const hubResAProj = trackerProjectBuy(hubEntry, resAId, desiredResA);
            const stResAProj = trackerProjectSell(st, resAId, desiredResA);
            const actualResA = Math.min(
                hubResAProj ? hubResAProj.quantity : 0,
                stResAProj ? stResAProj.quantity : 0
            );

            const hubResBProj = trackerProjectBuy(hubEntry, resBId, desiredResB);
            const stResBProj = trackerProjectSell(st, resBId, desiredResB);
            const actualResB = Math.min(
                hubResBProj ? hubResBProj.quantity : 0,
                stResBProj ? stResBProj.quantity : 0
            );

            if (actualResA <= 0 && actualResB <= 0) {
                stats.noStockRoom.push((st.name || '?') +
                    ' [st F room=' + (stResAProj ? stResAProj.quantity : 0) +
                    ', st W room=' + (stResBProj ? stResBProj.quantity : 0) +
                    ' | hub F sell=' + (hubResAProj ? hubResAProj.quantity : 0) +
                    ', hub W sell=' + (hubResBProj ? hubResBProj.quantity : 0) + ']');
                continue;
            }

            // Res_C qty = cargo freed by selling res_a+res_b.
            const desiredResC = actualResA + actualResB;
            const stResCProj = trackerProjectBuy(st, resCId, desiredResC);
            const hubEnergyProj = trackerProjectSell(hubEntry, resCId, desiredResC);
            const actualResC = Math.min(
                stResCProj ? stResCProj.quantity : 0,
                hubEnergyProj ? hubEnergyProj.quantity : 0
            );

            if (actualResC <= 0) {
                stats.noStockRoom.push((st.name || '?') +
                    ' [st E buyable=' + (stResCProj ? stResCProj.quantity : 0) +
                    ' | hub E room=' + (hubEnergyProj ? hubEnergyProj.quantity : 0) + ']');
                continue;
            }

            // Re-project with actual quantities for accurate curve pricing.
            const resABuy = trackerProjectBuy(hubEntry, resAId, actualResA);
            const resBBuy = trackerProjectBuy(hubEntry, resBId, actualResB);
            const resASell = trackerProjectSell(st, resAId, actualResA);
            const resBSell = trackerProjectSell(st, resBId, actualResB);
            const resCBuy = trackerProjectBuy(st, resCId, actualResC);
            const resCSell = trackerProjectSell(hubEntry, resCId, actualResC);

            const cost = (resABuy ? resABuy.totalCost : 0)
                       + (resBBuy ? resBBuy.totalCost : 0)
                       + (resCBuy ? resCBuy.totalCost : 0);
            const revenue = (resASell ? resASell.totalRevenue : 0)
                          + (resBSell ? resBSell.totalRevenue : 0)
                          + (resCSell ? resCSell.totalRevenue : 0);
            const profit = revenue - cost;

            // Round-trip travel AP (hub -> station -> hub). Same-sector via
            // Dijkstra; cross-sector via HPA* wormhole routing. Unknown → null
            // → '?' (no estimates, per AGENTS.md).
            let oneWayAp = null;
            if (sameSectorcycle && hubDijkstra) {
                const key = stationCoords.x + ',' + stationCoords.y;
                const d = (hubDijkstra[key] !== undefined) ? hubDijkstra[key] : null;
                if (d != null) oneWayAp = d;
            } else if (!sameSectorcycle && stSector && hubSector) {
                try {
                    oneWayAp = getCrossSectorAPFast(hubCoords, hubSector, stationCoords, stSector, null, null);
                } catch (e) { oneWayAp = null; }
            }
            const apCost = (oneWayAp != null) ? (oneWayAp * 2 + TRADE_AP) : null;
            const ratio = (apCost != null && apCost > 0) ? profit / apCost : null;

            routes.push({
                st: st,
                sector: stSector,
                coords: stationCoords,
                resAQty: actualResA,
                resBQty: actualResB,
                resCQty: actualResC,
                cost: cost,
                revenue: revenue,
                profit: profit,
                oneWayAp: oneWayAp,
                apCost: apCost,
                ratio: ratio
            });
            stats.qualified++;
        }

        routes.sort((a, b) => {
            if (a.ratio != null && b.ratio != null) return b.ratio - a.ratio;
            if (a.ratio != null) return -1;
            if (b.ratio != null) return 1;
            return (b.profit || 0) - (a.profit || 0);
        });

        return {
            routes: routes,
            hubEntry: hubEntry,
            hubSector: hubSector,
            hubCoords: hubCoords,
            resAId: resAId,
            resBId: resBId,
            resCId: resCId,
            maxCargo: maxCargo,
            desiredResA: desiredResA,
            desiredResB: desiredResB,
            usedFallback: usedFallback,
            stats: stats
        };
    }

    // >> Opportunities: one-way arbitrage
    //
    // Scans ALL tracked locations (not just configured export items) for
    // buy-low → sell-high pairs. For every commodity that at least one
    // location sells (buyFromObjPrice > 0) and another buys (sellToObjPrice
    // > 0), it projects a full-cargo buy at the seller and sell at the buyer,
    // then computes credit/AP via getCrossSectorAPFast (pre-calculated macro
    // wormhole graph + local Dijkstra). Only profitable routes (profit > 0)
    // are kept, sorted by cr/AP descending.
    //
    // Curve-aware pricing: trackerProjectBuy/Sell account for station/station
    // price curves when buying/selling in bulk. Buildings use flat pricing.
    //
    // AP model: travel (macro AP, asymmetric terrain) + TRADE_AP (10 = buy at
    // seller 5 + sell at buyer 5). Unlike the exports calculator (where TH
    // loading is free via manage), opportunities require actual
    // trade-form actions at both ends.
    function computeOpportunities() {
        __setOp('computeOpportunities');
        const maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;
        const TRADE_AP = 10;
        const minCrAp = parseFloat(GM_getValue('opps_min_crap', '0')) || 0;

        parseStaticMap(true);
        const store = getTrackerStore();
        if (Object.keys(store).length === 0) {
            return { error: 'No tracked locations yet. Open building/station/station trade screens to capture them.' };
        }

        // Build resId → { name, sellers: [...], buyers: [...] }
        const commodityIndex = {};
        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities) continue;
            const rc = realSectorAndCoords(e);
            if (!rc.coords) continue;

            for (const resId in e.commodities) {
                const c = e.commodities[resId];
                if (!c || !c.name) continue;

                if (!commodityIndex[resId]) {
                    commodityIndex[resId] = { name: c.name, sellers: [], buyers: [] };
                }
                if (c.buyFromObjPrice > 0) {
                    commodityIndex[resId].sellers.push({ entry: e, coords: rc.coords, sector: rc.sector });
                }
                if (c.sellToObjPrice > 0) {
                    commodityIndex[resId].buyers.push({ entry: e, coords: rc.coords, sector: rc.sector });
                }
            }
        }

        const dijCache = {};
        const routes = [];
        const usedFallback = false;
        let preFiltered = 0;
        const _projCache = new Map();
        const _proj = (entry, resId, qty, isBuy) => {
            const k = entry.userloc + '|' + resId + '|' + qty + '|' + (isBuy ? 'b' : 's');
            const hit = _projCache.get(k);
            if (hit !== undefined) return hit;
            const v = isBuy ? trackerProjectBuy(entry, resId, qty) : trackerProjectSell(entry, resId, qty);
            _projCache.set(k, v);
            return v;
        };

        for (const resId in commodityIndex) {
            const ci = commodityIndex[resId];
            if (ci.sellers.length === 0 || ci.buyers.length === 0) continue;

            for (const seller of ci.sellers) {
                for (const buyer of ci.buyers) {
                    if (seller.entry.userloc === buyer.entry.userloc) continue;

                    const buyProj = _proj(seller.entry, resId, maxCargo, true);
                    if (!buyProj || buyProj.quantity <= 0) continue;

                    const sellProj = _proj(buyer.entry, resId, maxCargo, false);
                    if (!sellProj || sellProj.quantity <= 0) continue;

                    const qty = Math.min(buyProj.quantity, sellProj.quantity);
                    if (qty <= 0) continue;

                    // Re-project with actual quantity for accurate curve pricing.
                    const finalBuy = _proj(seller.entry, resId, qty, true);
                    const finalSell = _proj(buyer.entry, resId, qty, false);
                    if (!finalBuy || !finalSell || finalBuy.quantity <= 0 || finalSell.quantity <= 0) continue;

                    const cost = finalBuy.totalCost;
                    const revenue = finalSell.totalRevenue;
                    const profit = revenue - cost;
                    if (profit <= 0) continue;

                    // Pre-filter: apCost >= TRADE_AP always, so if profit/TRADE_AP
                    // is already below threshold, cr/AP can never qualify. Skips the
                    // expensive getCrossSectorAPFast call entirely.
                    if (minCrAp > 0 && profit / TRADE_AP < minCrAp) { preFiltered++; continue; }

                    let ap = null;
                    try {
                        ap = getCrossSectorAPFast(seller.coords, seller.sector, buyer.coords, buyer.sector, dijCache, null);
                    } catch (e) { ap = null; }

                    const apCost = (ap != null) ? ap + TRADE_AP : null;
                    const ratio = (apCost != null && apCost > 0) ? profit / apCost : null;

                    // Post-filter: drop routes whose actual cr/AP is below threshold.
                    // Keep null-ratio routes (AP unknown) so user still sees them with '?'.
                    if (minCrAp > 0 && ratio != null && ratio < minCrAp) continue;

                    routes.push({
                        item: ci.name,
                        resId: resId,
                        seller: seller.entry,
                        buyer: buyer.entry,
                        sellerCoords: seller.coords,
                        buyerCoords: buyer.coords,
                        sellerSector: seller.sector,
                        buyerSector: buyer.sector,
                        units: qty,
                        buyPerUnit: finalBuy.perUnitAvg,
                        sellPerUnit: finalSell.perUnitAvg,
                        cost: cost,
                        revenue: revenue,
                        profit: profit,
                        travelAp: ap,
                        apCost: apCost,
                        ratio: ratio
                    });
                }
            }
        }

        routes.sort((a, b) => {
            if (a.ratio != null && b.ratio != null) return b.ratio - a.ratio;
            if (a.ratio != null) return -1;
            if (b.ratio != null) return 1;
            return (b.profit || 0) - (a.profit || 0);
        });

        return {
            routes: routes,
            maxCargo: maxCargo,
            usedFallback: usedFallback,
            commodityCount: Object.keys(commodityIndex).length,
            minCrAp: minCrAp,
            preFiltered: preFiltered
        };
    }

    // >> Opportunities: two-way arbitrage
    //
    // Finds location pairs A↔B where a round-trip is profitable:
    //   1. Buy X at A → travel A→B → sell X at B (forward leg)
    //   2. Buy Y at B → travel B→A → sell Y at A (return leg)
    // X and Y must be different commodities (same-commodity "round-trips"
    // reduce to a one-way arbitrage and are excluded).
    //
    // For each unordered pair (A, B), all profitable forward and return
    // commodities are collected, then the best (fwd, ret) pair with
    // different resIds is chosen — maximizing total round-trip profit.
    //
    // AP model: macro A→B + macro B→A (asymmetric terrain) + TRADE_AP (10
    // = combined sell+buy at each end, 5+5, steady-state). cr/AP = total
    // profit / total AP. Sorted by cr/AP descending.
    function computeTwoWayArbitrage() {
        __setOp('computeTwoWayArbitrage');
        const maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;
        const TRADE_AP = 10;
        const minCrAp = parseFloat(GM_getValue('opps_min_crap', '0')) || 0;

        parseStaticMap(true);
        const store = getTrackerStore();
        if (Object.keys(store).length === 0) {
            return { error: 'No tracked locations yet. Open building/station/station trade screens to capture them.' };
        }

        // Collect tracked locations with resolved coords.
        const locs = [];
        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities) continue;
            const rc = realSectorAndCoords(e);
            if (!rc.coords) continue;
            locs.push({ entry: e, coords: rc.coords, sector: rc.sector });
        }

        const dijCache = {};
        const routes = [];
        const usedFallback = false;
        let preFiltered = 0;
        const _projCache = new Map();
        const _proj = (entry, resId, qty, isBuy) => {
            const k = entry.userloc + '|' + resId + '|' + qty + '|' + (isBuy ? 'b' : 's');
            const hit = _projCache.get(k);
            if (hit !== undefined) return hit;
            const v = isBuy ? trackerProjectBuy(entry, resId, qty) : trackerProjectSell(entry, resId, qty);
            _projCache.set(k, v);
            return v;
        };

        for (let i = 0; i < locs.length; i++) {
            for (let j = i + 1; j < locs.length; j++) {
                const A = locs[i];
                const B = locs[j];

                // Collect profitable forward (A sells → B buys) and return
                // (B sells → A buys) commodity candidates.
                const fwdCandidates = [];
                const retCandidates = [];

                for (const resId in A.entry.commodities) {
                    const aComm = A.entry.commodities[resId];
                    if (!aComm || !aComm.name) continue;
                    const bComm = B.entry.commodities[resId];
                    if (!bComm) continue;

                    // Forward: A sells X (buyFromObjPrice), B buys X (sellToObjPrice).
                    if (aComm.buyFromObjPrice > 0 && bComm.sellToObjPrice > 0) {
                        const bp = _proj(A.entry, resId, maxCargo, true);
                        const sp = _proj(B.entry, resId, maxCargo, false);
                        if (bp && sp && bp.quantity > 0 && sp.quantity > 0) {
                            const q = Math.min(bp.quantity, sp.quantity);
                            const fb = _proj(A.entry, resId, q, true);
                            const fs = _proj(B.entry, resId, q, false);
                            if (fb && fs && fb.quantity > 0 && fs.quantity > 0) {
                                const p = fs.totalRevenue - fb.totalCost;
                                if (p > 0) fwdCandidates.push({
                                    resId: resId, name: aComm.name, qty: q, profit: p,
                                    buyPerUnit: fb.perUnitAvg, sellPerUnit: fs.perUnitAvg
                                });
                            }
                        }
                    }

                    // Return: B sells Y (buyFromObjPrice), A buys Y (sellToObjPrice).
                    if (aComm.sellToObjPrice > 0 && bComm.buyFromObjPrice > 0) {
                        const bp = _proj(B.entry, resId, maxCargo, true);
                        const sp = _proj(A.entry, resId, maxCargo, false);
                        if (bp && sp && bp.quantity > 0 && sp.quantity > 0) {
                            const q = Math.min(bp.quantity, sp.quantity);
                            const fb = _proj(B.entry, resId, q, true);
                            const fs = _proj(A.entry, resId, q, false);
                            if (fb && fs && fb.quantity > 0 && fs.quantity > 0) {
                                const p = fs.totalRevenue - fb.totalCost;
                                if (p > 0) retCandidates.push({
                                    resId: resId, name: aComm.name, qty: q, profit: p,
                                    buyPerUnit: fb.perUnitAvg, sellPerUnit: fs.perUnitAvg
                                });
                            }
                        }
                    }
                }

                if (fwdCandidates.length === 0 || retCandidates.length === 0) continue;

                fwdCandidates.sort((a, b) => b.profit - a.profit);
                retCandidates.sort((a, b) => b.profit - a.profit);

                // Find the best (fwd, ret) pair with different resIds.
                let bestTotal = -Infinity;
                let bestFwd = null, bestRet = null;
                for (const f of fwdCandidates) {
                    for (const r of retCandidates) {
                        if (f.resId === r.resId) continue;
                        const total = f.profit + r.profit;
                        if (total > bestTotal) {
                            bestTotal = total;
                            bestFwd = f;
                            bestRet = r;
                        }
                    }
                }
                if (!bestFwd || !bestRet) continue;

                // Pre-filter: apCost >= TRADE_AP, so if bestTotal/TRADE_AP is
                // below threshold, no point computing AP for this pair.
                if (minCrAp > 0 && bestTotal / TRADE_AP < minCrAp) { preFiltered++; continue; }

                // Macro AP both ways (the terrain is asymmetric).
                let apAB = null, apBA = null;
                try {
                    apAB = getCrossSectorAPFast(A.coords, A.sector, B.coords, B.sector, dijCache, null);
                    apBA = getCrossSectorAPFast(B.coords, B.sector, A.coords, A.sector, dijCache, null);
                } catch (e) { apAB = null; apBA = null; }

                const apCost = (apAB != null && apBA != null) ? apAB + apBA + TRADE_AP : null;
                const ratio = (apCost != null && apCost > 0) ? bestTotal / apCost : null;

                // Post-filter: drop routes below threshold (keep null-ratio).
                if (minCrAp > 0 && ratio != null && ratio < minCrAp) continue;

                routes.push({
                    A: A.entry,
                    B: B.entry,
                    Acoords: A.coords,
                    Bcoords: B.coords,
                    Asector: A.sector,
                    Bsector: B.sector,
                    fwdItem: bestFwd.name,
                    fwdResId: bestFwd.resId,
                    fwdQty: bestFwd.qty,
                    fwdProfit: bestFwd.profit,
                    fwdBuyPerUnit: bestFwd.buyPerUnit,
                    fwdSellPerUnit: bestFwd.sellPerUnit,
                    retItem: bestRet.name,
                    retResId: bestRet.resId,
                    retQty: bestRet.qty,
                    retProfit: bestRet.profit,
                    retBuyPerUnit: bestRet.buyPerUnit,
                    retSellPerUnit: bestRet.sellPerUnit,
                    profit: bestTotal,
                    travelApAB: apAB,
                    travelApBA: apBA,
                    apCost: apCost,
                    ratio: ratio
                });
            }
        }

        routes.sort((a, b) => {
            if (a.ratio != null && b.ratio != null) return b.ratio - a.ratio;
            if (a.ratio != null) return -1;
            if (b.ratio != null) return 1;
            return (b.profit || 0) - (a.profit || 0);
        });

        return {
            routes: routes,
            maxCargo: maxCargo,
            usedFallback: usedFallback,
            minCrAp: minCrAp,
            preFiltered: preFiltered
        };
    }

    // >> Opportunities: return exports for active run
    //
    // Given a from→to location pair, finds profitable commodities to buy at
    // 'from' and sell at 'to'. Used by the active run bar to show what's
    // worth bringing back in the reverse direction.
    function findReturnExports(fromEntry, toEntry, maxCargo) {
        if (!fromEntry || !toEntry || !fromEntry.commodities || !toEntry.commodities) return [];
        const results = [];
        for (const resId in fromEntry.commodities) {
            const fc = fromEntry.commodities[resId];
            if (!fc || !fc.name) continue;
            const tc = toEntry.commodities[resId];
            if (!tc) continue;
            if (fc.buyFromObjPrice <= 0 || tc.sellToObjPrice <= 0) continue;
            const bp = trackerProjectBuy(fromEntry, resId, maxCargo);
            const sp = trackerProjectSell(toEntry, resId, maxCargo);
            if (!bp || !sp || bp.quantity <= 0 || sp.quantity <= 0) continue;
            const q = Math.min(bp.quantity, sp.quantity);
            const fb = trackerProjectBuy(fromEntry, resId, q);
            const fs = trackerProjectSell(toEntry, resId, q);
            if (!fb || !fs || fb.quantity <= 0 || fs.quantity <= 0) continue;
            const profit = fs.totalRevenue - fb.totalCost;
            if (profit <= 0) continue;
            results.push({
                item: fc.name,
                resId: resId,
                qty: q,
                profit: profit,
                buyPerUnit: fb.perUnitAvg,
                sellPerUnit: fs.perUnitAvg
            });
        }
        results.sort((a, b) => b.profit - a.profit);
        return results;
    }

    // >> Opportunities: batch limit analysis
    //
    // Computes how many full-hull (maxCargo) batches are possible for a
    // single trade leg (buy at seller, sell at buyer), limited by three
    // constraints:
    //   1. Seller stock  — buyable units (stock - min) before seller runs out
    //   2. Buyer credits — how many batches buyer can pay for before money pool empties
    //   3. Buyer room    — free space + per-commodity max capacity at buyer
    //
    // Returns { batches, limits: { stk, cr, room }, bottleneck }.
    // Unknown constraints are omitted from limits; batches = min of known values.
    function computeBatchLimits(sellerEntry, buyerEntry, resId, maxCargo, sellRevPerBatch) {
        const limits = {};

        if (sellerEntry && sellerEntry.commodities && sellerEntry.commodities[resId]) {
            const sc = sellerEntry.commodities[resId];
            const buyable = Math.max(0, sc.stock - (sc.min || 0));
            limits.stk = buyable / maxCargo;
        }

        if (buyerEntry && buyerEntry.credits != null && sellRevPerBatch > 0) {
            limits.cr = buyerEntry.credits / sellRevPerBatch;
        }

        if (buyerEntry && buyerEntry.commodities && buyerEntry.commodities[resId]) {
            const bc = buyerEntry.commodities[resId];
            const stackRoom = (bc.max > 0) ? Math.max(0, bc.max - bc.stock) : Infinity;
            const spaceRoom = (buyerEntry.type === 'station' || buyerEntry.freeSpace == null || buyerEntry.freeSpace === Infinity)
                ? Infinity : Math.max(0, buyerEntry.freeSpace);
            const room = Math.min(stackRoom, spaceRoom);
            limits.room = (room === Infinity) ? Infinity : room / maxCargo;
        }

        let batches = Infinity;
        let bottleneck = null;
        for (const key in limits) {
            if (limits[key] < batches) {
                batches = limits[key];
                bottleneck = key;
            }
        }
        if (batches === Infinity) batches = null;
        return { batches: batches, limits: limits, bottleneck: bottleneck };
    }

    function fmtCr(n) {
        if (n == null || isNaN(n)) return '?';
        return simpleNumberFormatTracker(n);
    }
    function fmtRatio(r) {
        if (r == null || isNaN(r)) return '?';
        return (r >= 100 ? Math.round(r) : r.toFixed(1));
    }
    function fmtBat(n) {
        if (n == null) return '?';
        if (n === Infinity) return '\u221e';
        return n.toFixed(1);
    }

    function injectExportsCalculator() {
        const uiPos = GM_getValue('logistics_exports_ui_pos', { top: '50px', right: '6px' });

        const wrap = document.createElement('div');
        wrap.id = 'logistics-exports-panel';
        wrap.style.cssText = [
            'position:absolute',
            'top:' + uiPos.top,
            (uiPos.left != null ? 'left:' + uiPos.left : 'right:' + (uiPos.right || '6px')),
            'width:430px',
            'background-color:#00001C',
            'border:1px solid #aa7744',
            'font-family:Verdana,sans-serif',
            'font-size:10px',
            'color:#ccc',
            'z-index:9997',
            'box-shadow:2px 2px 10px rgba(0,0,0,0.8)'
        ].join(';');

        const header = document.createElement('div');
        header.style.cssText = 'background:#332200;padding:5px 7px;cursor:move;font-weight:bold;color:#ffaa55;border-bottom:1px solid #5a3a1a;user-select:none;';
        header.innerHTML = '\uD83D\uDCC8 Exports Calculator\u00a0\u00a0<span style="font-size:9px;color:#8a6a3a;">drag to move \u00b7 click to toggle</span>';
        wrap.appendChild(header);

        // Tab bar: switch between Exports and cycle views.
        let activeTab = 'exports';
        const tabBar = document.createElement('div');
        tabBar.style.cssText = 'display:flex;border-bottom:1px solid #5a3a1a;';
        wrap.appendChild(tabBar);

        function updateTabStyle() {
            [exportsTabBtn, cycleTabBtn, oppsTabBtn].forEach(btn => {
                const active = btn.dataset.tab === activeTab;
                btn.style.borderBottom = active ? '2px solid #ffaa55' : '2px solid transparent';
                btn.style.color = active ? '#ffcc77' : '#8a6a3a';
                btn.style.background = active ? '#332200' : '#1a1000';
            });
            // cfgBar (buy-price override) only applies to the Exports tab.
            cfgBar.style.display = (activeTab === 'exports' && !collapsed) ? 'flex' : 'none';
            // Sub-tab bar only applies to the Opportunities tab.
            if (oppSubBar) oppSubBar.style.display = (activeTab === 'opps' && !collapsed) ? 'flex' : 'none';
            // Exports sub-tab bar (TH vs Custom).
            if (expSubBar) expSubBar.style.display = (activeTab === 'exports' && !collapsed) ? 'flex' : 'none';
            if (expCustomBar) expCustomBar.style.display = (activeTab === 'exports' && expSubTab === 'custom' && !collapsed) ? 'flex' : 'none';
            if (expSubBar) updateExpSubTabStyle();
        }

        function makeTabBtn(label, tabId) {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.textContent = label;
            btn.dataset.tab = tabId;
            btn.style.cssText = 'flex:1;cursor:pointer;font-size:10px;padding:4px 8px;border:none;border-bottom:2px solid transparent;background:#1a1000;color:#8a6a3a;';
            btn.addEventListener('click', () => {
                activeTab = tabId;
                updateTabStyle();
                renderBody();
            });
            return btn;
        }
        const exportsTabBtn = makeTabBtn('Exports', 'exports');
        const cycleTabBtn = makeTabBtn('CYCLE', 'CYCLE');
        const oppsTabBtn = makeTabBtn('Opps', 'opps');
        tabBar.appendChild(exportsTabBtn);
        tabBar.appendChild(cycleTabBtn);
        tabBar.appendChild(oppsTabBtn);

        // Sub-tab bar for Opportunities (one-way vs two-way).
        let oppSubTab = 'oneway';
        const oppSubBar = document.createElement('div');
        oppSubBar.style.cssText = 'display:none;padding:3px 7px;border-bottom:1px solid #5a3a1a;gap:4px;';
        wrap.appendChild(oppSubBar);

        function makeSubTabBtn(label, subId) {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.textContent = label;
            btn.dataset.subtab = subId;
            btn.style.cssText = 'flex:1;cursor:pointer;font-size:9px;padding:2px 6px;border:1px solid #5a3a1a;background:#1a1000;color:#8a6a3a;';
            btn.addEventListener('click', () => {
                oppSubTab = subId;
                updateSubTabStyle();
                renderBody();
            });
            return btn;
        }
        const onewaySubBtn = makeSubTabBtn('One-way', 'oneway');
        const twowaySubBtn = makeSubTabBtn('Two-way', 'twoway');
        oppSubBar.appendChild(onewaySubBtn);
        oppSubBar.appendChild(twowaySubBtn);

        function updateSubTabStyle() {
            [onewaySubBtn, twowaySubBtn].forEach(btn => {
                const active = btn.dataset.subtab === oppSubTab;
                btn.style.color = active ? '#ffcc77' : '#8a6a3a';
                btn.style.background = active ? '#332200' : '#1a1000';
                btn.style.borderColor = active ? '#aa7744' : '#5a3a1a';
            });
        }

        // Sub-tab bar for Exports (TH vs Custom).
        let expSubTab = GM_getValue('exports_subtab', 'to');
        const expSubBar = document.createElement('div');
        expSubBar.style.cssText = 'display:none;padding:3px 7px;border-bottom:1px solid #5a3a1a;gap:4px;';
        wrap.appendChild(expSubBar);

        function makeExpSubTabBtn(label, subId) {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.textContent = label;
            btn.dataset.expsubtab = subId;
            btn.style.cssText = 'flex:1;cursor:pointer;font-size:9px;padding:2px 6px;border:1px solid #5a3a1a;background:#1a1000;color:#8a6a3a;';
            btn.addEventListener('click', () => {
                expSubTab = subId;
                GM_setValue('exports_subtab', subId);
                updateExpSubTabStyle();
                updateTabStyle();
                renderBody();
            });
            return btn;
        }
        const toSubBtn = makeExpSubTabBtn('TO', 'to');
        const customSubBtn = makeExpSubTabBtn('Custom', 'custom');
        expSubBar.appendChild(toSubBtn);
        expSubBar.appendChild(customSubBtn);

        function updateExpSubTabStyle() {
            [toSubBtn, customSubBtn].forEach(btn => {
                const active = btn.dataset.expsubtab === expSubTab;
                btn.style.color = active ? '#ffcc77' : '#8a6a3a';
                btn.style.background = active ? '#332200' : '#1a1000';
                btn.style.borderColor = active ? '#aa7744' : '#5a3a1a';
            });
        }

        // Custom export config bar: origin toggle, coords, sector, item, qty.
        const expCustomBar = document.createElement('div');
        expCustomBar.style.cssText = 'padding:4px 7px;border-bottom:1px solid #5a3a1a;display:none;gap:6px;align-items:center;flex-wrap:wrap;font-size:9px;';
        wrap.appendChild(expCustomBar);

        let expOriginMode = GM_getValue('exports_custom_origin', 'current');

        // Origin toggle buttons
        const originToggleLabel = document.createElement('span');
        originToggleLabel.textContent = 'Origin:';
        originToggleLabel.style.cssText = 'color:#8a6a3a;';
        expCustomBar.appendChild(originToggleLabel);

        function makeOriginBtn(label, mode) {
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.textContent = label;
            btn.dataset.originmode = mode;
            btn.style.cssText = 'cursor:pointer;font-size:9px;padding:2px 6px;border:1px solid #5a3a1a;background:#1a1000;color:#8a6a3a;';
            btn.addEventListener('click', () => {
                expOriginMode = mode;
                GM_setValue('exports_custom_origin', mode);
                updateOriginToggleStyle();
                expCoordsWrap.style.display = (mode === 'coords') ? 'flex' : 'none';
                renderBody();
            });
            return btn;
        }
        const originCurrentBtn = makeOriginBtn('Current', 'current');
        const originCoordsBtn = makeOriginBtn('Coords', 'coords');
        expCustomBar.appendChild(originCurrentBtn);
        expCustomBar.appendChild(originCoordsBtn);

        function updateOriginToggleStyle() {
            [originCurrentBtn, originCoordsBtn].forEach(btn => {
                const active = btn.dataset.originmode === expOriginMode;
                btn.style.color = active ? '#ffcc77' : '#8a6a3a';
                btn.style.background = active ? '#332200' : '#1a1000';
                btn.style.borderColor = active ? '#aa7744' : '#5a3a1a';
            });
        }
        updateOriginToggleStyle();

        // Coords + sector inputs (shown only in coords mode)
        const expCoordsWrap = document.createElement('div');
        expCoordsWrap.style.cssText = 'display:' + (expOriginMode === 'coords' ? 'flex' : 'none') + ';gap:4px;align-items:center;flex-wrap:wrap;';
        expCustomBar.appendChild(expCoordsWrap);

        const expCoordsInput = document.createElement('input');
        expCoordsInput.type = 'text';
        expCoordsInput.placeholder = 'x,y';
        expCoordsInput.title = 'Origin coordinates (e.g. 12,5)';
        expCoordsInput.value = GM_getValue('exports_custom_coords', '');
        expCoordsInput.style.cssText = 'width:50px;background:#1a1000;color:#ffaa55;border:1px solid #5a3a3a;font-size:9px;padding:2px 4px;';
        expCoordsWrap.appendChild(expCoordsInput);
        expCoordsInput.addEventListener('change', () => {
            GM_setValue('exports_custom_coords', expCoordsInput.value.trim());
            renderBody();
        });

        const expSectorInput = document.createElement('input');
        expSectorInput.type = 'text';
        expSectorInput.placeholder = 'sector';
        expSectorInput.title = 'Sector name (e.g. Sector-A, Sector-B)';
        expSectorInput.value = GM_getValue('exports_custom_sector', '');
        expSectorInput.style.cssText = 'width:90px;background:#1a1000;color:#ffaa55;border:1px solid #5a3a3a;font-size:9px;padding:2px 4px;';
        expCoordsWrap.appendChild(expSectorInput);
        expSectorInput.addEventListener('change', () => {
            GM_setValue('exports_custom_sector', expSectorInput.value.trim());
            renderBody();
        });

        // Item name input with datalist autocomplete
        const itemLabel = document.createElement('span');
        itemLabel.textContent = 'Item:';
        itemLabel.style.cssText = 'color:#8a6a3a;';
        expCustomBar.appendChild(itemLabel);

        const expItemInput = document.createElement('input');
        expItemInput.type = 'text';
        expItemInput.setAttribute('list', 'logistics-custom-item-list');
        expItemInput.placeholder = 'item name';
        expItemInput.title = 'Commodity to export (type the name)';
        expItemInput.value = GM_getValue('exports_custom_item', '');
        expItemInput.style.cssText = 'width:100px;background:#1a1000;color:#ffcc77;border:1px solid #5a3a3a;font-size:9px;padding:2px 4px;';
        expCustomBar.appendChild(expItemInput);
        expItemInput.addEventListener('change', () => {
            GM_setValue('exports_custom_item', expItemInput.value.trim());
            renderBody();
        });

        const expDatalist = document.createElement('datalist');
        expDatalist.id = 'logistics-custom-item-list';
        expCustomBar.appendChild(expDatalist);

        // Quantity input
        const qtyLabel = document.createElement('span');
        qtyLabel.textContent = 'Qty:';
        qtyLabel.style.cssText = 'color:#8a6a3a;';
        expCustomBar.appendChild(qtyLabel);

        const expQtyInput = document.createElement('input');
        expQtyInput.type = 'number';
        expQtyInput.min = '1';
        expQtyInput.placeholder = 'qty';
        expQtyInput.title = 'Units to transport for this export trip';
        expQtyInput.value = GM_getValue('exports_custom_qty', '');
        expQtyInput.style.cssText = 'width:50px;background:#1a1000;color:#88ccff;border:1px solid #5a3a3a;font-size:9px;padding:2px 4px;';
        expCustomBar.appendChild(expQtyInput);
        expQtyInput.addEventListener('change', () => {
            GM_setValue('exports_custom_qty', expQtyInput.value.trim());
            renderBody();
        });

        const cfgBar = document.createElement('div');
        cfgBar.style.cssText = 'padding:4px 7px;border-bottom:1px solid #5a3a1a;display:flex;gap:6px;align-items:center;flex-wrap:wrap;font-size:9px;';
        wrap.appendChild(cfgBar);

        const body = document.createElement('div');
        body.style.cssText = 'padding:5px 7px;max-height:560px;overflow:auto;';
        wrap.appendChild(body);

        const controls = document.createElement('div');
        controls.style.cssText = 'padding:5px 7px;border-top:1px solid #5a3a1a;display:flex;gap:4px;align-items:center;flex-wrap:wrap;';
        wrap.appendChild(controls);

        const buyInput = document.createElement('input');
        buyInput.type = 'number';
        buyInput.placeholder = 'buy price override';
        buyInput.title = 'Optional: override the default buy price (cheapest tracked producer). Leave blank to auto-detect.';
        buyInput.value = GM_getValue('config_export_buy_price', '');
        buyInput.style.cssText = 'width:110px;background:#1a1000;color:#ffaa55;border:1px solid #5a3a1a;font-size:9px;padding:2px 4px;';
        cfgBar.appendChild(buyInput);
        buyInput.addEventListener('change', () => {
            GM_setValue('config_export_buy_price', buyInput.value.trim());
            renderBody();
        });

        const refreshBtn = document.createElement('button');
        refreshBtn.type = 'button';
        refreshBtn.textContent = 'Recalculate';
        refreshBtn.style.cssText = 'cursor:pointer;font-size:10px;background:#332200;color:#ffcc77;border:1px solid #aa7744;padding:3px 8px;flex:1;';
        refreshBtn.addEventListener('click', () => renderBody(true));
        controls.appendChild(refreshBtn);

        const minCrApLabel = document.createElement('span');
        minCrApLabel.textContent = 'Min cr/AP:';
        minCrApLabel.style.cssText = 'color:#8a6a3a;font-size:9px;';
        controls.appendChild(minCrApLabel);

        const minCrApInput = document.createElement('input');
        minCrApInput.type = 'number';
        minCrApInput.min = '0';
        minCrApInput.placeholder = '0';
        minCrApInput.title = 'Minimum credits per AP. Routes below this cr/AP are skipped during computation (saves pathfinding). 0 = no filter.';
        minCrApInput.value = GM_getValue('opps_min_crap', '0');
        minCrApInput.style.cssText = 'width:60px;background:#1a1000;color:#ffcc77;border:1px solid #5a3a1a;font-size:9px;padding:2px 4px;';
        controls.appendChild(minCrApInput);
        minCrApInput.addEventListener('change', () => {
            const v = parseFloat(minCrApInput.value) || 0;
            GM_setValue('opps_min_crap', String(v));
            // Clear cache so Recalculate picks up the new threshold.
            oppsCache.oneway = null;
            oppsCache.twoway = null;
            GM_deleteValue('opps_cache_v1');
            renderBody();
        });

        let oppsCache = GM_getValue('opps_cache_v1', null);
        if (!oppsCache) oppsCache = { oneway: null, twoway: null };
        function saveOppsCache() {
            try { GM_setValue('opps_cache_v1', oppsCache); } catch (e) { /* too large */ }
        }
        let oppsActiveRun = GM_getValue('opps_active_run_v1', null);

        // Floating active-run bar (separate from panel, draggable).
        // Created once; renderActiveRunBar() updates its content/visibility.
        const runBar = document.createElement('div');
        runBar.id = 'logistics-opps-runbar';
        const rbPos = GM_getValue('logistics_opps_runbar_pos', { top: '60px', left: '460px' });
        runBar.style.cssText = [
            'position:fixed',
            'top:' + (rbPos.top || '60px'),
            'left:' + (rbPos.left || '460px'),
            'width:400px',
            'background-color:#00001C',
            'border:1px solid #2a5a2a',
            'font-family:Verdana,sans-serif',
            'font-size:10px',
            'color:#ccc',
            'z-index:10001',
            'display:none'
        ].join(';');

        let rbDragging = false, rbMoved = false, rbStartX = 0, rbStartY = 0, rbInitX = 0, rbInitY = 0;
        runBar.addEventListener('mousedown', function(e) {
            if (e.target.closest('.opps-clear-run') || e.target.closest('.opps-active-fly')) return;
            rbDragging = true;
            rbMoved = false;
            rbStartX = e.clientX; rbStartY = e.clientY;
            rbInitX = runBar.offsetLeft; rbInitY = runBar.offsetTop;
            e.preventDefault();
        });
        document.addEventListener('mousemove', function(e) {
            if (!rbDragging) return;
            var dx = e.clientX - rbStartX;
            var dy = e.clientY - rbStartY;
            if (Math.abs(dx) > 2 || Math.abs(dy) > 2) rbMoved = true;
            runBar.style.left = (rbInitX + dx) + 'px';
            runBar.style.top = (rbInitY + dy) + 'px';
        });
        document.addEventListener('mouseup', function() {
            if (!rbDragging) return;
            rbDragging = false;
            if (rbMoved) {
                GM_setValue('logistics_opps_runbar_pos', { top: runBar.style.top, left: runBar.style.left });
            }
        });

        runBar.addEventListener('click', function(e) {
            if (e.target.closest('.opps-clear-run')) {
                oppsActiveRun = null;
                GM_deleteValue('opps_active_run_v1');
                renderActiveRunBar();
                return;
            }
            var el = e.target.closest('.opps-active-fly');
            if (!el) return;
            var run = oppsActiveRun;
            if (!run) return;
            try {
                if (run.subTab === 'oneway') {
                    if (el.dataset.target === 'seller') {
                        flyToCoords({ x: run.sellerCoords.x, y: run.sellerCoords.y, sector: run.sellerSector }, run.sellerName + ' [' + run.sellerCoords.x + ',' + run.sellerCoords.y + ']');
                    } else {
                        flyToCoords({ x: run.buyerCoords.x, y: run.buyerCoords.y, sector: run.buyerSector }, run.buyerName + ' [' + run.buyerCoords.x + ',' + run.buyerCoords.y + ']');
                    }
                } else {
                    if (el.dataset.target === 'A') {
                        flyToCoords({ x: run.Acoords.x, y: run.Acoords.y, sector: run.Asector }, run.Aname + ' [' + run.Acoords.x + ',' + run.Acoords.y + ']');
                    } else {
                        flyToCoords({ x: run.Bcoords.x, y: run.Bcoords.y, sector: run.Bsector }, run.Bname + ' [' + run.Bcoords.x + ',' + run.Bcoords.y + ']');
                    }
                }
            } catch(ex) { console.error('[logistics-opps] fly error:', ex); }
        });

        function renderBody(force) {
            renderActiveRunBar();
            if (activeTab === 'CYCLE') rendercycleBody();
            else if (activeTab === 'opps') renderOpportunitiesBody(force);
            else {
                if (expSubTab === 'custom') renderCustomExportsBody();
                else renderExportsBody();
            }
        }

        function buildExportsRouteTable(routes) {
            const t = document.createElement('table');
            t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;';
            t.innerHTML = '<tr style="color:#8a6a3a;">' +
                '<th style="text-align:left;">#</th>' +
                '<th style="text-align:left;">Item</th>' +
                '<th style="text-align:left;">Destination</th>' +
                '<th>Units</th>' +
                '<th>Buy</th>' +
                '<th>Sell</th>' +
                '<th>Profit</th>' +
                '<th>AP</th>' +
                '<th>cr/AP</th>' +
                '</tr>';
            routes.forEach((r, i) => {
                const tr = document.createElement('tr');
                tr.style.cssText = 'border-bottom:1px dashed #2a2a1a;color:#bbb;';
                const typeIcon = r.dest.type === 'station' ? '\u25cf' : (r.dest.type === 'station' ? '\u25b2' : '\u25a0');
                const typeColor = r.dest.type === 'station' ? '#aaffaa' : (r.dest.type === 'station' ? '#88ccff' : '#ffcc88');
                const sameTag = r.sameSector ? '' : ' <span style="color:#5a5a3a;">(cross-sector)</span>';
                const packTag = r.packed ? ' <span style="color:#cc88ff;">(packaging)</span>' : '';
                const apTxt = (r.apCost == null)
                    ? '<span style="color:#666;">?</span>'
                    : (r.packed
                        ? '<span style="color:#ffaa44;">' + r.apCost + '</span><span style="color:#5a5a3a;"> (incl. 400 pack)</span>'
                        : '<span style="color:#ffaa44;">' + r.apCost + '</span>');
                const ratioTxt = (r.ratio == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#00ff88;font-weight:bold;">' + fmtRatio(r.ratio) + '</span>';
                const profitTxt = (r.profit == null)
                    ? '<span style="color:#666;">' + fmtCr(r.revenue) + '*</span>'
                    : '<span style="color:' + (r.profit < 0 ? '#ff5555' : '#88ff88') + ';">' + fmtCr(r.profit) + '</span>';
                const nameAttrs = ' class="export-fly-target" data-idx="' + i + '" title="Click to fly here" style="color:' + typeColor + ';cursor:pointer;text-decoration:underline;"';
                tr.innerHTML =
                    '<td>' + (i + 1) + '</td>' +
                    '<td style="color:#ffcc77;">' + r.item + '</td>' +
                    '<td><span style="color:' + typeColor + ';">' + typeIcon + '</span> ' +
                        '<span' + nameAttrs + '>' + (r.dest.name || '?') + '</span> ' +
                        '<span style="color:#666;">[' + r.coords.x + ',' + r.coords.y + ']' +
                        (r.sector ? ' ' + r.sector : '') + sameTag + '</span></td>' +
                    '<td style="text-align:right;">' + r.units + packTag + '</td>' +
                    '<td style="text-align:right;color:#ffaa55;">' + (r.buyPrice != null ? fmtCr(r.buyPrice) : '?') + '</td>' +
                    '<td style="text-align:right;color:#88cc88;">' + fmtCr(r.sellPerUnit) + '</td>' +
                    '<td style="text-align:right;">' + profitTxt + '</td>' +
                    '<td style="text-align:right;color:#ffaa44;">' + apTxt + '</td>' +
                    '<td style="text-align:right;">' + ratioTxt + '</td>';
                t.appendChild(tr);
            });
            t.addEventListener('click', function(e) {
                const el = e.target.closest('.export-fly-target');
                if (!el) return;
                const idx = parseInt(el.dataset.idx, 10);
                const r = routes[idx];
                if (!r) return;
                flyToCoords({ x: r.coords.x, y: r.coords.y, sector: r.sector }, (r.dest.name || '?') + ' [' + r.coords.x + ',' + r.coords.y + ']');
            });
            return t;
        }

        function renderExportsBody() {
            body.innerHTML = '';
            const res = computeExportRoutes();

            if (res.error) {
                body.innerHTML = '<div style="color:#ff8866;padding:6px;text-align:center;">' + res.error + '</div>';
                return;
            }

            const toName = res.toEntry ? (res.toEntry.name || 'TO') : '(TH not tracked)';
            const toCoordStr = '[' + res.toCoords.x + ',' + res.toCoords.y + ']';
            let sumHtml = '<div style="margin-bottom:4px;">' +
                '<span style="color:#88ccff;">TO:</span> ' + toName + ' ' + toCoordStr +
                (res.toSector ? ' <span style="color:#666;">' + res.toSector + '</span>' : '') +
                (res.toEntry ? '' : ' <span style="color:#ff8866;">(open TH trade screen to capture stock)</span>') +
                '</div>';

            const items = Object.keys(res.itemInfo);
            if (items.length > 0) {
                sumHtml += '<div style="color:#aaa;margin-bottom:4px;">';
                for (const it of items) {
                    const info = res.itemInfo[it];
                    if (info.note) {
                        sumHtml += '<div style="color:#ff8866;">' + it + ': ' + info.note + '</div>';
                    } else {
                        sumHtml += '<div>' +
                            '<span style="color:#ffcc77;">' + it + '</span>' +
                            ' \u00b7 buy <span style="color:#ffaa55;">' + (info.buyPrice != null ? fmtCr(info.buyPrice) : '?') + '</span>' +
                            (info.buySource ? ' <span style="color:#666;">(' + info.buySource + ')</span>' : '') +
                            ' \u00b7 TH stock <span style="color:#88ccff;">' + (info.toStock != null ? info.toStock : '?') + '</span>' +
                            '</div>';
                    }
                }
                sumHtml += '</div>';
            }
            if (res.usedFallback) {
                sumHtml += '<div style="color:#8a6a3a;margin-bottom:4px;">\u26a0 No sector map data \u2014 AP unavailable (?). Load map_data.txt.</div>';
            }
            const sumDiv = document.createElement('div');
            sumDiv.innerHTML = sumHtml;
            body.appendChild(sumDiv);

            if (res.routes.length === 0) {
                const empty = document.createElement('div');
                empty.style.cssText = 'color:#888;text-align:center;padding:8px;';
                empty.textContent = 'No buyers found for the configured export items. Open more station/station trade screens to capture them.';
                body.appendChild(empty);
                return;
            }

            body.appendChild(buildExportsRouteTable(res.routes));

            const note = document.createElement('div');
            note.style.cssText = 'color:#5a5a3a;font-size:8px;margin-top:4px;';
            note.innerHTML = 'Click a destination name to auto-fly there. Cross-sector flights use wormhole routing. One-way AP from TH via equip_f (same-sector Dijkstra or cross-sector HPA*). "?" only when equip_f data is missing or the target is unreachable. Sell = price buyer pays you. *revenue shown (no buy price). cr/AP = net profit per AP.<br><span style="color:#5a5a3a;">(packaging) = D&gt;400 AP + buyer room&gt;200: 400 AP overhead doubles cargo to 400 for that trip (apCost = D+400). Finite 400-package stock not depleted across ranked routes.</span>';
            body.appendChild(note);
        }

        function renderCustomExportsBody() {
            body.innerHTML = '';

            // Populate datalist with tracked commodity names (cheap; rebuild only if count changed)
            const store0 = getTrackerStore();
            const nameMap0 = buildExportNameToResIdMap(store0);
            const trackedNames = Object.keys(nameMap0).sort();
            if (expDatalist.childElementCount !== trackedNames.length) {
                expDatalist.innerHTML = trackedNames.map(n => '<option value="' + n.charAt(0).toUpperCase() + n.slice(1) + '">').join('');
            }

            const opts = {
                originMode: expOriginMode,
                coordsStr: expCoordsInput.value.trim(),
                sectorStr: expSectorInput.value.trim(),
                itemName: expItemInput.value.trim(),
                qty: expQtyInput.value.trim(),
                buyOverride: parseInt(GM_getValue('config_export_buy_price', ''), 10)
            };
            const res = computeCustomExportRoutes(opts);

            if (res.error) {
                body.innerHTML = '<div style="color:#ff8866;padding:6px;text-align:center;">' + res.error + '</div>';
                return;
            }

            // Summary
            const originLabel = opts.originMode === 'current' ? 'Current position' : 'Coords';
            let sumHtml = '<div style="margin-bottom:4px;">' +
                '<span style="color:#88ccff;">Origin:</span> ' + originLabel +
                ' <span style="color:#666;">[' + res.originCoords.x + ',' + res.originCoords.y + ']</span>' +
                (res.originSector ? ' <span style="color:#666;">' + res.originSector + '</span>' : '') +
                '</div>';
            sumHtml += '<div style="color:#aaa;margin-bottom:4px;">' +
                '<span style="color:#ffcc77;">' + res.itemName + '</span>' +
                ' \u00b7 qty <span style="color:#88ccff;">' + res.qty + '</span>' +
                ' \u00b7 buy <span style="color:#ffaa55;">' + (res.buyPrice != null ? fmtCr(res.buyPrice) : '?') + '</span>' +
                (res.buySource ? ' <span style="color:#666;">(' + res.buySource + ')</span>' : '') +
                '</div>';
            if (res.usedFallback) {
                sumHtml += '<div style="color:#8a6a3a;margin-bottom:4px;">\u26a0 No sector map data \u2014 AP unavailable (?). Load map_data.txt.</div>';
            }
            const sumDiv = document.createElement('div');
            sumDiv.innerHTML = sumHtml;
            body.appendChild(sumDiv);

            if (res.routes.length === 0) {
                const empty = document.createElement('div');
                empty.style.cssText = 'color:#888;text-align:center;padding:8px;';
                empty.textContent = 'No buyers found for ' + res.itemName + '. Open more station/station trade screens to capture them.';
                body.appendChild(empty);
                return;
            }

            body.appendChild(buildExportsRouteTable(res.routes));

            const note = document.createElement('div');
            note.style.cssText = 'color:#5a5a3a;font-size:8px;margin-top:4px;';
            note.innerHTML = 'One-way export from the chosen origin. Click a destination name to auto-fly there. AP = travel (same-sector Dijkstra or cross-sector HPA* wormhole routing). "?" when equip_f data is missing or target unreachable. Units capped by quantity, buyer room, and cargo capacity. (packaging) = D&gt;400 AP + buyer room&gt;200: 400 AP overhead doubles cargo for that trip.';
            body.appendChild(note);
        }

        function rendercycleBody() {
            body.innerHTML = '';
            const res = computecycleRoutes();

            if (res.error) {
                body.innerHTML = '<div style="color:#ff8866;padding:6px;text-align:center;">' + res.error + '</div>';
                return;
            }

            const hubName = res.hubEntry.name || 'Hub';
            const hubCoordStr = '[' + res.hubCoords.x + ',' + res.hubCoords.y + ']';
            let sumHtml = '<div style="margin-bottom:4px;">' +
                '<span style="color:#aaffaa;">Hub:</span> ' + hubName + ' ' + hubCoordStr +
                (res.hubSector ? ' <span style="color:#666;">' + res.hubSector + '</span>' : '') +
                '</div>';
            sumHtml += '<div style="color:#aaa;margin-bottom:4px;">' +
                'Cargo <span style="color:#88ccff;">' + res.maxCargo + '</span> ' +
                '\u00b7 Res_A/Res_B split <span style="color:#ffcc77;">' + res.desiredResA + '</span>/' +
                '<span style="color:#88ccff;">' + res.desiredResB + '</span> ' +
                '<span style="color:#666;">(123:84 ratio)</span>' +
                '</div>';
            if (res.usedFallback) {
                sumHtml += '<div style="color:#8a6a3a;margin-bottom:4px;">\u26a0 No sector map data \u2014 AP unavailable (?). Load map_data.txt.</div>';
            }
            body.innerHTML = sumHtml;

            if (res.routes.length === 0) {
                const st = res.stats || {};
                const lines = [];
                lines.push('No qualifying cycle stations in the hub sector.');
                lines.push('Tracked stations: ' + (st.totalStations || 0) +
                    ' \u00b7 qualified: ' + (st.qualified || 0));
                if (st.totalStations === 0) {
                    lines.push('No stations captured yet \u2014 open station trade screens (/app/trade3) to capture them.');
                } else {
                    if (st.crossSector && st.crossSector.length) {
                        lines.push('Unresolved tiles (' + st.crossSector.length + '): ' + st.crossSector.join(', ') +
                            '\n  (tile IDs that couldn\'t be mapped to sector/coords — re-open the station trade screen to capture them)');
                    }
                    if (st.missingCommodity && st.missingCommodity.length) {
                        lines.push('Missing Res_A/Res_B/E data (' + st.missingCommodity.length + '): ' + st.missingCommodity.join(', ') +
                            '\n  Re-open those station trade screens to capture res_a/res_b/res_c rows.');
                    }
                    if (st.noPrice && st.noPrice.length) {
                        lines.push('Price 0 / not traded (' + st.noPrice.length + '): ' + st.noPrice.join(', '));
                    }
                    if (st.noStockRoom && st.noStockRoom.length) {
                        lines.push('No stock/cargo room (' + st.noStockRoom.length + '): ' + st.noStockRoom.join(', ') +
                            '\n  st = station, hub = hub station. room = space to buy/sell.');
                    }
                    if (st.isHub) {
                        lines.push('(' + st.isHub + ' entry is the hub itself)');
                    }
                }
                const empty = document.createElement('div');
                empty.style.cssText = 'color:#888;padding:8px;font-size:9px;white-space:pre-line;line-height:1.5;';
                empty.textContent = lines.join('\n');
                body.appendChild(empty);
                return;
            }

            const t = document.createElement('table');
            t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;';
            t.innerHTML = '<tr style="color:#8a6a3a;">' +
                '<th style="text-align:left;">#</th>' +
                '<th style="text-align:left;">Station</th>' +
                '<th>Res_A</th>' +
                '<th>Res_B</th>' +
                '<th>Res_C</th>' +
                '<th>Profit</th>' +
                '<th>AP</th>' +
                '<th>cr/AP</th>' +
                '</tr>';

            res.routes.forEach((r, i) => {
                const tr = document.createElement('tr');
                tr.style.cssText = 'border-bottom:1px dashed #2a2a1a;color:#bbb;';
                const profitColor = r.profit < 0 ? '#ff5555' : '#88ff88';
                const ratioTxt = (r.ratio == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#00ff88;font-weight:bold;">' + fmtRatio(r.ratio) + '</span>';
                tr.innerHTML =
                    '<td>' + (i + 1) + '</td>' +
                    '<td><span style="color:#88ccff;">\u25b2</span> ' +
                        '<span class="export-fly-target" data-idx="' + i + '" title="Click to fly here" style="color:#88ccff;cursor:pointer;text-decoration:underline;">' + (r.st.name || '?') + '</span> ' +
                        '<span style="color:#666;">[' + r.coords.x + ',' + r.coords.y + ']</span></td>' +
                    '<td style="text-align:right;color:#ffcc77;">' + r.resAQty + '</td>' +
                    '<td style="text-align:right;color:#88ccff;">' + r.resBQty + '</td>' +
                    '<td style="text-align:right;color:#ffaa55;">' + r.resCQty + '</td>' +
                    '<td style="text-align:right;color:' + profitColor + ';">' + fmtCr(r.profit) + '</td>' +
                    '<td style="text-align:right;color:#ffaa44;">' + (r.apCost == null ? '<span style="color:#666;">?</span>' : r.apCost) + '</td>' +
                    '<td style="text-align:right;">' + ratioTxt + '</td>';
                t.appendChild(tr);
            });
            t.addEventListener('click', function(e) {
                const el = e.target.closest('.export-fly-target');
                if (!el) return;
                const idx = parseInt(el.dataset.idx, 10);
                const r = res.routes[idx];
                if (!r) return;
                flyToCoords(r.coords, (r.st.name || '?') + ' [' + r.coords.x + ',' + r.coords.y + ']');
            });
            body.appendChild(t);

            const note = document.createElement('div');
            note.style.cssText = 'color:#5a5a3a;font-size:8px;margin-top:4px;';
            note.innerHTML = 'resupply cycle: buy res_a+res_b at hub (123:84 ratio) \u2192 travel to station \u2192 sell res_a+res_b, buy res_c \u2192 travel back \u2192 sell res_c at hub. AP = round-trip travel + 10 (2 combined trade actions). Quantities are capped by stock/capacity limits. Click a station name to auto-fly there. Only same-sector stations are listed.';
            body.appendChild(note);
        }

        // >> Opportunities: active run bar (floating, draggable)
        //
        // When the user pins a route (via "pin" button or clicking a name),
        // it becomes the active run. The bar floats as a separate draggable
        // window outside the exports panel, persisting across recalculates
        // and tab switches until cleared.
        function renderActiveRunBar() {
            var run = oppsActiveRun;
            if (!run) { runBar.style.display = 'none'; runBar.innerHTML = ''; return; }
            runBar.style.display = 'block';

            var inner = '';
            inner += '<div style="cursor:move;padding:3px 7px;border-bottom:1px solid #2a5a2a;background:#0a1a0a;">' +
                '<span style="color:#00ff88;font-weight:bold;">\uD83D\uDCCC Active Run</span>' +
                '<button type="button" class="opps-clear-run" style="float:right;cursor:pointer;font-size:8px;background:#330000;color:#ff8866;border:1px solid #5a0000;padding:1px 5px;">Clear</button>' +
                '</div>';
            inner += '<div style="padding:5px 7px;">';

            if (run.subTab === 'oneway') {
                inner += '<div style="color:#ccc;">' +
                    'Buy <span style="color:#ffcc77;">' + run.item + '</span> at ' +
                    '<span class="opps-active-fly" data-target="seller" title="Sector: ' + (run.sellerSector||'?') + '" style="color:#aaffaa;cursor:pointer;text-decoration:underline;">' + run.sellerName + ' [' + run.sellerCoords.x + ',' + run.sellerCoords.y + ']</span>' +
                    ' \u2192 Sell at ' +
                    '<span class="opps-active-fly" data-target="buyer" title="Sector: ' + (run.buyerSector||'?') + '" style="color:#88ccff;cursor:pointer;text-decoration:underline;">' + run.buyerName + ' [' + run.buyerCoords.x + ',' + run.buyerCoords.y + ']</span>' +
                    '</div>';
                inner += '<div style="color:#888;font-size:8px;margin-top:1px;">' + run.units + 'u \u00b7 buy ' + fmtCr(run.buyPerUnit) + ' \u00b7 sell ' + fmtCr(run.sellPerUnit) + ' \u00b7 profit ' + fmtCr(run.profit) + ' cr</div>';
            } else {
                inner += '<div style="color:#ccc;">' +
                    'Buy <span style="color:#ffcc77;">' + run.fwdItem + '</span> at ' +
                    '<span class="opps-active-fly" data-target="A" title="Sector: ' + (run.Asector||'?') + '" style="color:#aaffaa;cursor:pointer;text-decoration:underline;">' + run.Aname + ' [' + run.Acoords.x + ',' + run.Acoords.y + ']</span>' +
                    ' \u2192 Sell ' + run.fwdItem + ' / Buy <span style="color:#88ccff;">' + run.retItem + '</span> at ' +
                    '<span class="opps-active-fly" data-target="B" title="Sector: ' + (run.Bsector||'?') + '" style="color:#88ccff;cursor:pointer;text-decoration:underline;">' + run.Bname + ' [' + run.Bcoords.x + ',' + run.Bcoords.y + ']</span>' +
                    ' \u2192 Sell ' + run.retItem + ' at ' +
                    '<span class="opps-active-fly" data-target="A" title="Sector: ' + (run.Asector||'?') + '" style="color:#aaffaa;cursor:pointer;text-decoration:underline;">' + run.Aname + '</span>' +
                    '</div>';
                inner += '<div style="color:#888;font-size:8px;margin-top:1px;">Fwd: ' + run.fwdQty + ' ' + run.fwdItem + ' (+' + fmtCr(run.fwdProfit) + ') \u00b7 Ret: ' + run.retQty + ' ' + run.retItem + ' (+' + fmtCr(run.retProfit) + ') \u00b7 Total: ' + fmtCr(run.profit) + ' cr</div>';
            }

            var maxCargo = parseInt(GM_getValue('config_max_cargo', '200'), 10) || 200;
            var store = getTrackerStore();

            if (run.subTab === 'oneway' && run.sellerLoc != null && run.buyerLoc != null && run.resId != null) {
                var sellerEntry = store[String(run.sellerLoc)];
                var buyerEntry = store[String(run.buyerLoc)];
                var sellRevPerBatch = (run.sellPerUnit || 0) * maxCargo;
                var bl = computeBatchLimits(sellerEntry, buyerEntry, run.resId, maxCargo, sellRevPerBatch);
                if (bl.batches != null) {
                    var parts = [];
                    if (bl.limits.stk != null) parts.push((bl.bottleneck === 'stk' ? '<span style="color:#ff6644;font-weight:bold;">' : '<span style="color:#5a5a3a;">') + 'stk:' + fmtBat(bl.limits.stk) + '</span>');
                    if (bl.limits.cr != null) parts.push((bl.bottleneck === 'cr' ? '<span style="color:#ff6644;font-weight:bold;">' : '<span style="color:#5a5a3a;">') + 'cr:' + fmtBat(bl.limits.cr) + '</span>');
                    if (bl.limits.room != null) parts.push((bl.bottleneck === 'room' ? '<span style="color:#ff6644;font-weight:bold;">' : '<span style="color:#5a5a3a;">') + 'room:' + (bl.limits.room === Infinity ? '\u221e' : fmtBat(bl.limits.room)) + '</span>');
                    inner += '<div style="font-size:8px;margin-top:1px;">Laps: <span style="color:#ffaa44;font-weight:bold;">' + fmtBat(bl.batches) + '</span> ' + parts.join(' \u00b7 ') + '</div>';
                }
            } else if (run.subTab === 'twoway' && run.Aloc != null && run.Bloc != null && run.fwdResId != null && run.retResId != null) {
                var aEntry = store[String(run.Aloc)];
                var bEntry = store[String(run.Bloc)];
                var fwdSellRev = (run.fwdSellPerUnit || 0) * maxCargo;
                var retSellRev = (run.retSellPerUnit || 0) * maxCargo;
                var fwdBL = computeBatchLimits(aEntry, bEntry, run.fwdResId, maxCargo, fwdSellRev);
                var retBL = computeBatchLimits(bEntry, aEntry, run.retResId, maxCargo, retSellRev);
                var vals = [];
                if (fwdBL.batches != null) vals.push(fwdBL.batches);
                if (retBL.batches != null) vals.push(retBL.batches);
                if (vals.length > 0) {
                    var batches = Math.min.apply(null, vals);
                    var bnLabels = [];
                    if (fwdBL.batches === batches && fwdBL.bottleneck) bnLabels.push('fwd ' + fwdBL.bottleneck);
                    if (retBL.batches === batches && retBL.bottleneck) bnLabels.push('ret ' + retBL.bottleneck);
                    inner += '<div style="font-size:8px;margin-top:1px;">Laps: <span style="color:#ffaa44;font-weight:bold;">' + fmtBat(batches) + '</span> <span style="color:#5a5a3a;">' + (bnLabels.length ? bnLabels.join(', ') + '-limited' : '') + '</span></div>';
                }
            }

            var fromLoc = null, toLoc = null;
            if (run.subTab === 'oneway') {
                fromLoc = run.buyerLoc;
                toLoc = run.sellerLoc;
            } else {
                fromLoc = run.Bloc;
                toLoc = run.Aloc;
            }
            if (fromLoc != null && toLoc != null) {
                var fromEntry = store[String(fromLoc)];
                var toEntry = store[String(toLoc)];
                var returns = findReturnExports(fromEntry, toEntry, maxCargo);
                if (returns.length > 0 && run.apCost != null && run.apCost > 0) {
                    var retNames = returns.map(function(r) { return r.item; });
                    if (retNames.length > 3) retNames = retNames.slice(0, 3).concat(['+' + (retNames.length - 3) + ' more']);
                    var totalRetProfit = returns.reduce(function(s, r) { return s + r.profit; }, 0);
                    var crap = totalRetProfit / run.apCost;
                    inner += '<div class="opps-return-exports" style="color:#8a6a3a;font-size:8px;margin-top:2px;">Return: <span style="color:#ffcc77;">' + retNames.join(', ') + '</span> \u00b7 <span style="color:#00ff88;font-weight:bold;">' + fmtRatio(crap) + '</span> cr/AP</div>';
                } else if (returns.length > 0) {
                    var retNames2 = returns.map(function(r) { return r.item; });
                    inner += '<div class="opps-return-exports" style="color:#8a6a3a;font-size:8px;margin-top:2px;">Return: <span style="color:#ffcc77;">' + retNames2.join(', ') + '</span> (AP unknown)</div>';
                } else {
                    inner += '<div class="opps-return-exports" style="color:#5a3a1a;font-size:8px;margin-top:2px;">Return: \u2014</div>';
                }
            }

            inner += '</div>';
            runBar.innerHTML = inner;
        }

        // >> Opportunities tab renderer
        // Opps computation is O(n²×commodities) with macro AP lookups — too
        // heavy to re-run on every tab switch. Results are cached per sub-tab;
        // only the Recalculate button forces a recompute.
        function renderOpportunitiesBody(force) {
            body.innerHTML = '';
            updateSubTabStyle();
            if (oppSubTab === 'twoway') {
                if (force) { oppsCache.twoway = computeTwoWayArbitrage(); saveOppsCache(); }
                if (oppsCache.twoway) renderTwoWayOpps(oppsCache.twoway);
                else {
                    const empty = document.createElement('div');
                    empty.style.cssText = 'color:#888;text-align:center;padding:12px;';
                    empty.textContent = 'No two-way data. Press Recalculate to scan for arbitrage routes.';
                    body.appendChild(empty);
                }
            } else {
                if (force) { oppsCache.oneway = computeOpportunities(); saveOppsCache(); }
                if (oppsCache.oneway) renderOneWayOpps(oppsCache.oneway);
                else {
                    const empty = document.createElement('div');
                    empty.style.cssText = 'color:#888;text-align:center;padding:12px;';
                    empty.textContent = 'No one-way data. Press Recalculate to scan for arbitrage routes.';
                    body.appendChild(empty);
                }
            }
        }

        function renderOneWayOpps(res) {
            if (res.error) {
                body.innerHTML = '<div style="color:#ff8866;padding:6px;text-align:center;">' + res.error + '</div>';
                return;
            }

            let html = '<div style="margin-bottom:4px;color:#aaa;">' +
                'One-way arbitrage: buy low \u2192 sell high. ' +
                '<span style="color:#88ccff;">' + res.routes.length + '</span> profitable routes' +
                ' across <span style="color:#88ccff;">' + res.commodityCount + '</span> tracked commodities' +
                ' (cargo <span style="color:#ffcc77;">' + res.maxCargo + '</span>).';
            if (res.minCrAp > 0) {
                html += ' <span style="color:#8a6a3a;">Min cr/AP: <b style="color:#ffcc77;">' + res.minCrAp + '</b>' +
                    (res.preFiltered > 0 ? ' (' + res.preFiltered + ' pairs skipped)' : '') +
                    '</span>';
            }
            html += '</div>';
            if (res.usedFallback) {
                html += '<div style="color:#8a6a3a;margin-bottom:4px;">\u26a0 No sector map data \u2014 AP unavailable (?). Load map_data.txt.</div>';
            }
            const sumDiv = document.createElement('div');
            sumDiv.innerHTML = html;
            body.appendChild(sumDiv);

            if (res.routes.length === 0) {
                const empty = document.createElement('div');
                empty.style.cssText = 'color:#888;text-align:center;padding:8px;';
                empty.textContent = 'No profitable one-way routes found. Open more trade screens to capture prices.';
                body.appendChild(empty);
                return;
            }

            const t = document.createElement('table');
            t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;';
            t.innerHTML = '<tr style="color:#8a6a3a;">' +
                '<th style="text-align:left;">#</th>' +
                '<th style="text-align:left;">Item</th>' +
                '<th style="text-align:left;">From \u2192 To</th>' +
                '<th>Qty</th>' +
                '<th>Buy</th>' +
                '<th>Sell</th>' +
                '<th>Profit</th>' +
                '<th>AP</th>' +
                '<th>cr/AP</th>' +
                '<th>Laps</th>' +
                '</tr>';

            const store = getTrackerStore();
            res.routes.forEach((r, i) => {
                const tr = document.createElement('tr');
                tr.style.cssText = 'border-bottom:1px dashed #2a2a1a;color:#bbb;';
                const sIcon = r.seller.type === 'station' ? '\u25cf' : (r.seller.type === 'station' ? '\u25b2' : '\u25a0');
                const bIcon = r.buyer.type === 'station' ? '\u25cf' : (r.buyer.type === 'station' ? '\u25b2' : '\u25a0');
                const sColor = r.seller.type === 'station' ? '#aaffaa' : (r.seller.type === 'station' ? '#88ccff' : '#ffcc88');
                const bColor = r.buyer.type === 'station' ? '#aaffaa' : (r.buyer.type === 'station' ? '#88ccff' : '#ffcc88');
                const apTxt = (r.apCost == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#ffaa44;">' + r.apCost + '</span>';
                const ratioTxt = (r.ratio == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#00ff88;font-weight:bold;">' + fmtRatio(r.ratio) + '</span>';
                const sellRevPerBatch = (r.sellPerUnit || 0) * res.maxCargo;
                const sellerEntry = store[String(r.seller.userloc)];
                const buyerEntry = store[String(r.buyer.userloc)];
                const bl = computeBatchLimits(sellerEntry, buyerEntry, r.resId, res.maxCargo, sellRevPerBatch);
                let lapsTxt;
                if (bl.batches != null) {
                    lapsTxt = '<span style="color:#ffaa44;font-weight:bold;">' + fmtBat(bl.batches) + '</span>' +
                        '<br><span style="color:#ff6644;font-size:8px;">' + bl.bottleneck + '</span>';
                } else {
                    lapsTxt = '<span style="color:#666;">?</span>';
                }
                tr.innerHTML =
                    '<td>' + (i + 1) + ' <span class="opps-pin" data-idx="' + i + '" style="cursor:pointer;color:#8a6a3a;font-size:8px;">pin</span></td>' +
                    '<td style="color:#ffcc77;">' + r.item + '</td>' +
                    '<td><span style="color:' + sColor + ';">' + sIcon + '</span> ' +
                        '<span class="export-fly-target" data-idx="' + i + '" data-target="seller" title="Sector: ' + r.sellerSector + ' (click to fly)" style="color:' + sColor + ';cursor:pointer;text-decoration:underline;">' + (r.seller.name || '?') + '</span>' +
                        ' <span style="color:#5a5a3a;">[' + r.sellerCoords.x + ',' + r.sellerCoords.y + ']</span>' +
                        ' <span style="color:#8a6a3a;">\u2192</span> ' +
                        '<span style="color:' + bColor + ';">' + bIcon + '</span> ' +
                        '<span class="export-fly-target" data-idx="' + i + '" data-target="buyer" title="Sector: ' + r.buyerSector + ' (click to fly)" style="color:' + bColor + ';cursor:pointer;text-decoration:underline;">' + (r.buyer.name || '?') + '</span>' +
                        ' <span style="color:#5a5a3a;">[' + r.buyerCoords.x + ',' + r.buyerCoords.y + ']</span></td>' +
                    '<td style="text-align:right;">' + r.units + '</td>' +
                    '<td style="text-align:right;color:#ffaa55;">' + fmtCr(r.buyPerUnit) + '</td>' +
                    '<td style="text-align:right;color:#88cc88;">' + fmtCr(r.sellPerUnit) + '</td>' +
                    '<td style="text-align:right;color:#88ff88;">' + fmtCr(r.profit) + '</td>' +
                    '<td style="text-align:right;color:#ffaa44;">' + apTxt + '</td>' +
                    '<td style="text-align:right;">' + ratioTxt + '</td>' +
                    '<td style="text-align:center;">' + lapsTxt + '</td>';
                t.appendChild(tr);
            });
            t.addEventListener('click', function(e) {
                var pinEl = e.target.closest('.opps-pin');
                if (pinEl) {
                    var idx = parseInt(pinEl.dataset.idx, 10);
                    var r = res.routes[idx];
                    if (!r) return;
                    oppsActiveRun = {
                        subTab: 'oneway',
                        item: r.item,
                        resId: r.resId,
                        sellerName: r.seller.name || '?',
                        sellerCoords: r.sellerCoords,
                        sellerSector: r.sellerSector,
                        sellerLoc: r.seller.userloc,
                        buyerName: r.buyer.name || '?',
                        buyerCoords: r.buyerCoords,
                        buyerSector: r.buyerSector,
                        buyerLoc: r.buyer.userloc,
                        units: r.units,
                        profit: r.profit,
                        apCost: r.apCost,
                        buyPerUnit: r.buyPerUnit,
                        sellPerUnit: r.sellPerUnit
                    };
                    GM_setValue('opps_active_run_v1', oppsActiveRun);
                    renderActiveRunBar();
                    return;
                }
                var el = e.target.closest('.export-fly-target');
                if (!el) return;
                var idx = parseInt(el.dataset.idx, 10);
                var r = res.routes[idx];
                if (!r) return;
                oppsActiveRun = {
                    subTab: 'oneway',
                    item: r.item,
                    resId: r.resId,
                    sellerName: r.seller.name || '?',
                    sellerCoords: r.sellerCoords,
                    sellerSector: r.sellerSector,
                    sellerLoc: r.seller.userloc,
                    buyerName: r.buyer.name || '?',
                    buyerCoords: r.buyerCoords,
                    buyerSector: r.buyerSector,
                    buyerLoc: r.buyer.userloc,
                    units: r.units,
                    profit: r.profit,
                    apCost: r.apCost,
                    buyPerUnit: r.buyPerUnit,
                    sellPerUnit: r.sellPerUnit
                };
                GM_setValue('opps_active_run_v1', oppsActiveRun);
                renderBody(false);
                try {
                    if (el.dataset.target === 'seller') {
                        flyToCoords({ x: r.sellerCoords.x, y: r.sellerCoords.y, sector: r.sellerSector }, (r.seller.name || '?') + ' [' + r.sellerCoords.x + ',' + r.sellerCoords.y + ']');
                    } else {
                        flyToCoords({ x: r.buyerCoords.x, y: r.buyerCoords.y, sector: r.buyerSector }, (r.buyer.name || '?') + ' [' + r.buyerCoords.x + ',' + r.buyerCoords.y + ']');
                    }
                } catch(e) { console.error('[logistics-opps] fly error:', e); }
            });
            body.appendChild(t);

            const note = document.createElement('div');
            note.style.cssText = 'color:#5a5a3a;font-size:8px;margin-top:4px;';
            note.innerHTML = 'Buy at seller \u2192 travel \u2192 sell at buyer. Profitable routes only (profit &gt; 0). AP = travel (macro wormhole AP, asymmetric terrain) + 10 (buy 5 + sell 5). Buy/Sell = per-unit average (curve-aware for planets/stations). Laps = full-hull trips before bottleneck (stk=seller stock, cr=buyer credits, room=buyer room). Click <b>pin</b> to set as active run. Click a name to auto-fly and pin.';
            body.appendChild(note);
        }

        function renderTwoWayOpps(res) {
            if (res.error) {
                body.innerHTML = '<div style="color:#ff8866;padding:6px;text-align:center;">' + res.error + '</div>';
                return;
            }

            let html = '<div style="margin-bottom:4px;color:#aaa;">' +
                'Two-way arbitrage: A\u2194B round-trip. ' +
                '<span style="color:#88ccff;">' + res.routes.length + '</span> profitable pairs' +
                ' (cargo <span style="color:#ffcc77;">' + res.maxCargo + '</span>).';
            if (res.minCrAp > 0) {
                html += ' <span style="color:#8a6a3a;">Min cr/AP: <b style="color:#ffcc77;">' + res.minCrAp + '</b>' +
                    (res.preFiltered > 0 ? ' (' + res.preFiltered + ' pairs skipped)' : '') +
                    '</span>';
            }
            html += '</div>';
            if (res.usedFallback) {
                html += '<div style="color:#8a6a3a;margin-bottom:4px;">\u26a0 No sector map data \u2014 AP unavailable (?). Load map_data.txt.</div>';
            }
            const sumDiv2 = document.createElement('div');
            sumDiv2.innerHTML = html;
            body.appendChild(sumDiv2);

            if (res.routes.length === 0) {
                const empty = document.createElement('div');
                empty.style.cssText = 'color:#888;text-align:center;padding:8px;';
                empty.textContent = 'No profitable two-way arbitrage pairs found. Need at least two locations that sell different commodities each other buys.';
                body.appendChild(empty);
                return;
            }

            const t = document.createElement('table');
            t.style.cssText = 'width:100%;border-collapse:collapse;font-size:9px;';
            t.innerHTML = '<tr style="color:#8a6a3a;">' +
                '<th style="text-align:left;">#</th>' +
                '<th style="text-align:left;">A \u2194 B</th>' +
                '<th>\u2192Fwd</th>' +
                '<th>\u2190Ret</th>' +
                '<th>Profit</th>' +
                '<th>AP</th>' +
                '<th>cr/AP</th>' +
                '<th>Laps</th>' +
                '</tr>';

            const store = getTrackerStore();
            res.routes.forEach((r, i) => {
                const tr = document.createElement('tr');
                tr.style.cssText = 'border-bottom:1px dashed #2a2a1a;color:#bbb;';
                const aIcon = r.A.type === 'station' ? '\u25cf' : (r.A.type === 'station' ? '\u25b2' : '\u25a0');
                const bIcon = r.B.type === 'station' ? '\u25cf' : (r.B.type === 'station' ? '\u25b2' : '\u25a0');
                const aColor = r.A.type === 'station' ? '#aaffaa' : (r.A.type === 'station' ? '#88ccff' : '#ffcc88');
                const bColor = r.B.type === 'station' ? '#aaffaa' : (r.B.type === 'station' ? '#88ccff' : '#ffcc88');
                const apTxt = (r.apCost == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#ffaa44;">' + r.apCost + '</span>';
                const ratioTxt = (r.ratio == null)
                    ? '<span style="color:#666;">?</span>'
                    : '<span style="color:#00ff88;font-weight:bold;">' + fmtRatio(r.ratio) + '</span>';
                const aEntry = store[String(r.A.userloc)];
                const bEntry = store[String(r.B.userloc)];
                const fwdSellRev = (r.fwdSellPerUnit || 0) * res.maxCargo;
                const retSellRev = (r.retSellPerUnit || 0) * res.maxCargo;
                const fwdBL = computeBatchLimits(aEntry, bEntry, r.fwdResId, res.maxCargo, fwdSellRev);
                const retBL = computeBatchLimits(bEntry, aEntry, r.retResId, res.maxCargo, retSellRev);
                const blVals = [];
                if (fwdBL.batches != null) blVals.push(fwdBL.batches);
                if (retBL.batches != null) blVals.push(retBL.batches);
                let lapsTxt;
                if (blVals.length > 0) {
                    const laps = Math.min.apply(null, blVals);
                    const bnLabels = [];
                    if (fwdBL.batches === laps && fwdBL.bottleneck) bnLabels.push('fwd ' + fwdBL.bottleneck);
                    if (retBL.batches === laps && retBL.bottleneck) bnLabels.push('ret ' + retBL.bottleneck);
                    lapsTxt = '<span style="color:#ffaa44;font-weight:bold;">' + fmtBat(laps) + '</span>' +
                        '<br><span style="color:#ff6644;font-size:8px;">' + bnLabels.join(', ') + '</span>';
                } else {
                    lapsTxt = '<span style="color:#666;">?</span>';
                }
                tr.innerHTML =
                    '<td>' + (i + 1) + ' <span class="opps-pin" data-idx="' + i + '" style="cursor:pointer;color:#8a6a3a;font-size:8px;">pin</span></td>' +
                    '<td><span style="color:' + aColor + ';">' + aIcon + '</span> ' +
                        '<span class="export-fly-target" data-idx="' + i + '" data-target="A" title="Sector: ' + r.Asector + ' (click to fly)" style="color:' + aColor + ';cursor:pointer;text-decoration:underline;">' + (r.A.name || '?') + '</span>' +
                        ' <span style="color:#5a5a3a;">[' + r.Acoords.x + ',' + r.Acoords.y + ']</span>' +
                        ' <span style="color:#8a6a3a;">\u2194</span> ' +
                        '<span style="color:' + bColor + ';">' + bIcon + '</span> ' +
                        '<span class="export-fly-target" data-idx="' + i + '" data-target="B" title="Sector: ' + r.Bsector + ' (click to fly)" style="color:' + bColor + ';cursor:pointer;text-decoration:underline;">' + (r.B.name || '?') + '</span>' +
                        ' <span style="color:#5a5a3a;">[' + r.Bcoords.x + ',' + r.Bcoords.y + ']</span></td>' +
                    '<td style="text-align:right;color:#ffcc77;">' + r.fwdItem + '<br><span style="color:#5a5a3a;">' + r.fwdQty + 'u +' + fmtCr(r.fwdProfit) + '</span></td>' +
                    '<td style="text-align:right;color:#88ccff;">' + r.retItem + '<br><span style="color:#5a5a3a;">' + r.retQty + 'u +' + fmtCr(r.retProfit) + '</span></td>' +
                    '<td style="text-align:right;color:#88ff88;">' + fmtCr(r.profit) + '</td>' +
                    '<td style="text-align:right;color:#ffaa44;">' + apTxt + '</td>' +
                    '<td style="text-align:right;">' + ratioTxt + '</td>' +
                    '<td style="text-align:center;">' + lapsTxt + '</td>';
                t.appendChild(tr);
            });
            t.addEventListener('click', function(e) {
                var pinEl = e.target.closest('.opps-pin');
                if (pinEl) {
                    var idx = parseInt(pinEl.dataset.idx, 10);
                    var r = res.routes[idx];
                    if (!r) return;
                    oppsActiveRun = {
                        subTab: 'twoway',
                        Aname: r.A.name || '?',
                        Acoords: r.Acoords,
                        Asector: r.Asector,
                        Aloc: r.A.userloc,
                        Bname: r.B.name || '?',
                        Bcoords: r.Bcoords,
                        Bsector: r.Bsector,
                        Bloc: r.B.userloc,
                        fwdItem: r.fwdItem,
                        fwdResId: r.fwdResId,
                        fwdQty: r.fwdQty,
                        fwdProfit: r.fwdProfit,
                        fwdSellPerUnit: r.fwdSellPerUnit,
                        retItem: r.retItem,
                        retResId: r.retResId,
                        retQty: r.retQty,
                        retProfit: r.retProfit,
                        retSellPerUnit: r.retSellPerUnit,
                        profit: r.profit,
                        apCost: r.apCost
                    };
                    GM_setValue('opps_active_run_v1', oppsActiveRun);
                    renderActiveRunBar();
                    return;
                }
                var el = e.target.closest('.export-fly-target');
                if (!el) return;
                var idx = parseInt(el.dataset.idx, 10);
                var r = res.routes[idx];
                if (!r) return;
                oppsActiveRun = {
                    subTab: 'twoway',
                    Aname: r.A.name || '?',
                    Acoords: r.Acoords,
                    Asector: r.Asector,
                    Aloc: r.A.userloc,
                    Bname: r.B.name || '?',
                    Bcoords: r.Bcoords,
                    Bsector: r.Bsector,
                    Bloc: r.B.userloc,
                    fwdItem: r.fwdItem,
                    fwdResId: r.fwdResId,
                    fwdQty: r.fwdQty,
                    fwdProfit: r.fwdProfit,
                    fwdSellPerUnit: r.fwdSellPerUnit,
                    retItem: r.retItem,
                    retResId: r.retResId,
                    retQty: r.retQty,
                    retProfit: r.retProfit,
                    retSellPerUnit: r.retSellPerUnit,
                    profit: r.profit,
                    apCost: r.apCost
                };
                GM_setValue('opps_active_run_v1', oppsActiveRun);
                renderBody(false);
                try {
                    if (el.dataset.target === 'A') {
                        flyToCoords({ x: r.Acoords.x, y: r.Acoords.y, sector: r.Asector }, (r.A.name || '?') + ' [' + r.Acoords.x + ',' + r.Acoords.y + ']');
                    } else {
                        flyToCoords({ x: r.Bcoords.x, y: r.Bcoords.y, sector: r.Bsector }, (r.B.name || '?') + ' [' + r.Bcoords.x + ',' + r.Bcoords.y + ']');
                    }
                } catch(e) { console.error('[logistics-opps] fly error:', e); }
            });
            body.appendChild(t);

            const note = document.createElement('div');
            note.style.cssText = 'color:#5a5a3a;font-size:8px;margin-top:4px;';
            note.innerHTML = 'Round-trip: buy X at A \u2192 travel A\u2192B \u2192 sell X, buy Y at B \u2192 travel B\u2192A \u2192 sell Y at A. AP = macro A\u2192B + macro B\u2192A (asymmetric) + 10 (combined sell+buy at each end, steady-state). Best forward (X) and return (Y) commodities chosen per pair (X\u2260Y). Laps = round-trips before bottleneck (fwd/ret stk/cr/room). Click <b>pin</b> to set as active run. Click a name to auto-fly and pin.';
            body.appendChild(note);
        }

        // Drag logic (header: move, or click to toggle collapse).
        let collapsed = false;
        let isDragging = false, dragMoved = false, startX = 0, startY = 0, initialX = 0, initialY = 0;

        header.addEventListener('mousedown', (e) => {
            isDragging = true;
            dragMoved = false;
            startX = e.clientX; startY = e.clientY;
            initialX = wrap.offsetLeft; initialY = wrap.offsetTop;
            e.preventDefault();
        });
        document.addEventListener('mousemove', (e) => {
            if (!isDragging) return;
            const dx = e.clientX - startX, dy = e.clientY - startY;
            if (Math.abs(dx) > 3 || Math.abs(dy) > 3) dragMoved = true;
            wrap.style.left = (initialX + dx) + 'px';
            wrap.style.top = (initialY + dy) + 'px';
            wrap.style.right = 'auto';
        });
        document.addEventListener('mouseup', () => {
            if (!isDragging) return;
            isDragging = false;
            if (dragMoved) {
                GM_setValue('logistics_exports_ui_pos', { top: wrap.style.top, left: wrap.style.left });
            } else {
                collapsed = !collapsed;
                body.style.display = collapsed ? 'none' : 'block';
                tabBar.style.display = collapsed ? 'none' : 'flex';
                controls.style.display = collapsed ? 'none' : 'flex';
                updateTabStyle();
            }
        });

        updateTabStyle();
        const mount = document.body || document.documentElement;
        if (mount) {
            mount.appendChild(wrap);
            mount.appendChild(runBar);
        }
        renderBody();
        console.log('[logistics-exports] panel injected on', currentPath);
    }

    // --- 13. Ship Config & Terrain Costs ---
     // >> Equipment-aware terrain AP costs (ported from a third-party calculator)
     // Base AP per terrain type (char-keyed), before ship equipment adjustments.
     // f=type_a, e=type_b, g=type_c, o=type_d, v=type_e, m=type_f, b=blocked.
     const BASE_TERRAIN_AP = { f: 11, e: 20, g: 16, o: 25, v: 18, m: 36, b: Infinity };

     // Default ship options.  drive 6 + nav 3 reproduces the previously
     // hard-coded terrainAP for f/e/g/o; v and m are now correct (the old
     // static values v:13, m:11 were stale placeholders).  Overridable via
     // GM_setValue config_ship_* (set in the fly-here ship-config section).
     const DEFAULT_SHIP_OPTIONS = {
         drive_speed: 6,
         navigation_level: 3,
         equip_e: false,
         equip_f: 'none',       // 'none' | 'primary' | 'secondary'
         boost: false,
         equip_a: false,
         equip_b: 'none',         // 'none' | 'weak' | 'strong'
         equip_c: 'none',      // 'none' | 'weak' | 'strong'
         equip_d: 0,       // 0 | 1 | 2  (reduces type_e terrain cost)
         wormhole_cost: 10,
         wormhole_seal: 'none',    // 'none'|'seal_a'|'seal_b'|'seal_c'|'wh-closed-A'|...
         equip_h: false,
     };

     function getShipOptions() {
         return {
             drive_speed:      GM_getValue('config_ship_drive_speed', DEFAULT_SHIP_OPTIONS.drive_speed),
             navigation_level: GM_getValue('config_ship_navigation_level', DEFAULT_SHIP_OPTIONS.navigation_level),
             equip_e:       GM_getValue('config_ship_equip_e', DEFAULT_SHIP_OPTIONS.equip_e),
             equip_f:       GM_getValue('config_ship_equip_f', DEFAULT_SHIP_OPTIONS.equip_f),
             boost:            GM_getValue('config_ship_boost', DEFAULT_SHIP_OPTIONS.boost),
             equip_a:          GM_getValue('config_ship_equip_a', DEFAULT_SHIP_OPTIONS.equip_a),
             equip_b:         GM_getValue('config_ship_equip_b', DEFAULT_SHIP_OPTIONS.equip_b),
             equip_c:      GM_getValue('config_ship_equip_c', DEFAULT_SHIP_OPTIONS.equip_c),
             equip_d:  GM_getValue('config_ship_equip_d', DEFAULT_SHIP_OPTIONS.equip_d),
             wormhole_cost:    GM_getValue('config_ship_wormhole_cost', DEFAULT_SHIP_OPTIONS.wormhole_cost),
             wormhole_seal:    GM_getValue('config_ship_wormhole_seal', DEFAULT_SHIP_OPTIONS.wormhole_seal),
             // NOTE: config_ship_equip_h has NO UI control — the Fly Here
             // ship-config panel deliberately omits it. It is only settable via
             // a manual GM_setValue('config_ship_equip_h', true) and defaults
             // to false. Kept for equip_h-storm support / future UI.
             equip_h:        GM_getValue('config_ship_equip_h', DEFAULT_SHIP_OPTIONS.equip_h),
         };
     }

     // Pure function: given ship options, return a char-keyed AP cost map.
     // Mirrors getTileCosts() from the outsourced a third-party calculator client.
     function computeTileCosts(options, equip_h) {
         const o = options || DEFAULT_SHIP_OPTIONS;
         const costs = { f: BASE_TERRAIN_AP.f, e: BASE_TERRAIN_AP.e, g: BASE_TERRAIN_AP.g,
                         o: BASE_TERRAIN_AP.o, v: BASE_TERRAIN_AP.v, m: BASE_TERRAIN_AP.m };

         const nav = Number(o.navigation_level) || 0;
         if (nav >= 3) costs.e -= 1;
         if (nav >= 2) costs.g -= 1;
         if (nav >= 1) costs.o -= 1;

         const drive = Number(o.drive_speed) || 0;
         const sf = !!equip_h || !!o.equip_h;
         for (const k in costs) {
             costs[k] -= drive;
             if (o.equip_e) costs[k] -= 1;
             if (o.boost) costs[k] += 2;
             if (o.equip_a) costs[k] += 1;
             if (sf) costs[k] += 3;
         }

         if (o.equip_c === 'strong') costs.e -= 2;
         else if (o.equip_c === 'weak') costs.e -= 1;
         if (o.equip_b === 'strong') costs.g -= 2;
         else if (o.equip_b === 'weak') costs.g -= 1;

         const vp = Number(o.equip_d) || 0;
         if (vp > 0) costs.v -= vp;

         if (o.equip_f === 'primary') {
             for (const k in costs) costs[k] = Math.ceil(costs[k] * 0.66);
         } else if (o.equip_f === 'secondary') {
             for (const k in costs) costs[k] = Math.ceil(costs[k] * 0.83);
         }

         costs.b = Infinity;
         return costs;
     }

     // Cached terrain AP map for the current ship options.
     let _terrainAPCache = null, _terrainAPCacheKey = null;
     function getTerrainAP() {
         const o = getShipOptions();
         const key = JSON.stringify(o);
         if (_terrainAPCacheKey === key && _terrainAPCache) return _terrainAPCache;
         _terrainAPCache = computeTileCosts(o, false);
         _terrainAPCacheKey = key;
         return _terrainAPCache;
     }

    // --- 14. Local Sector equip_f ---

    function parseStaticMap(silent = false) {
        let rawMapData = localStorage.getItem("logistics_static_map_data") || "PASTE_YOUR_STATICXT_TXT_HERE";
        if (!rawMapData || rawMapData.includes("PASTE_YOUR_STATICXT_TXT_HERE")) {
            return false;
        }
        if (Object.keys(parsedMap).length > 0) return true;
        const lines = rawMapData.split(/[\r\n]+/);
        let currentSectorName = null;
        for (let line of lines) {
            line = line.trim();
            if (!line) continue;
            if (line.startsWith("sector ")) {
                let parts = line.substring(7).split(":");
                currentSectorName = parts[0].replace(/_/g, " ");
                parsedMap[currentSectorName] = { grid: [], wormholes: {}, beacons: [], stations: [] };
            } else if (line.startsWith("wh ")) {
                let parts = line.split(" ");
                let parts1 = parts[1].replace(/_/g, " ");
                let hashIdx = parts1.indexOf("#");
                let whDest = hashIdx >= 0 ? parts1.substring(0, hashIdx) : parts1;
                let whSub = hashIdx >= 0 ? parts1.substring(hashIdx + 1) : null;
                if (!parsedMap[currentSectorName].wormholes[whDest]) {
                    parsedMap[currentSectorName].wormholes[whDest] = [];
                }
                parsedMap[currentSectorName].wormholes[whDest].push({ x: parseInt(parts[2], 10), y: parseInt(parts[3], 10), sub: whSub });
            } else if (line.startsWith("beacon ")) {
                let parts = line.split(" ");
                parsedMap[currentSectorName].beacons.push({ x: parseInt(parts[parts.length - 2], 10), y: parseInt(parts[parts.length - 1], 10) });
            } else if (line.startsWith("station ")) {
                let parts = line.split(/\s+/);
                let y = parseInt(parts[parts.length - 1], 10);
                let x = parseInt(parts[parts.length - 2], 10);
                if (!isNaN(x) && !isNaN(y)) {
                    if (!parsedMap[currentSectorName].stations) parsedMap[currentSectorName].stations = [];
                    if (!parsedMap[currentSectorName].stations.some((st) => st.x === x && st.y === y)) {
                        parsedMap[currentSectorName].stations.push({ x, y, name: parts.slice(1, -2).join(" ") || "Station" });
                    }
                }
            } else if (currentSectorName && /^\S{4,}$/.test(line) && !/^(sector|wh|beacon|station)\b/i.test(line)) {
                parsedMap[currentSectorName].grid.push(line.toLowerCase().split(""));
            }
        }

        // Pad grids to SECTOR_DATA dimensions with 'b' (blocked, NEVER 'f').
        // HPA's hpaParseMap does the same — this keeps parsedMap consistent
        // for callers that read it directly (logisticsGetSectorPath fallback,
        // test harnesses). No merge: fragments stay as separate entries.
        for (const name in parsedMap) {
            const secInfo = getSectorData(name);
            if (!secInfo) continue;
            const tRows = secInfo.rows, tCols = secInfo.cols;
            const grid = parsedMap[name].grid;
            if (grid.length === 0) continue;
            while (grid.length < tRows) grid.push(new Array(tCols).fill('b'));
            for (let i = 0; i < grid.length; i++) {
                while (grid[i].length < tCols) grid[i].push('b');
            }
        }
        return Object.keys(parsedMap).length > 0;
    }

    function getSectorPath(sectorName, startX, startY, endX, endY) {
        const table = hpaGetTable();
        if (!table) return null;
        const fromFrag = hpaResolveFragment(table.sectors, sectorName, startX, startY);
        const toFrag = hpaResolveFragment(table.sectors, sectorName, endX, endY);
        if (fromFrag !== toFrag) return null;
        const sec = table.sectors.get(fromFrag);
        if (!sec || sec.grid.length === 0) return null;
        return hpaLocalAStar(sec.grid, table.terrainAP, startX, startY, endX, endY);
    }

    function logisticsGetSectorPath(sectorName, startTileId, startX, startY, endX, endY) {
        let path = getSectorPath(sectorName, startX, startY, endX, endY);
        if (!path) return null;
        let sector = parsedMap[sectorName];
        let secInfo = getSectorData(sectorName);
        let rows = secInfo ? secInfo.rows : sector.grid.length;
        let sectorStart = startTileId - (startX * rows + startY);
        let tileIds = path.map((p) => sectorStart + p.x * rows + p.y);
        return { path: path, tileIds: tileIds };
    }

    // >> Tile ID ↔ sector/coords helpers
    // Tile IDs are contiguous within a sector: tileId = start + x*rows + y
    // SECTOR_DATA is declared in the sector-map static-data part (earlier in
    // the IIFE); the try/catch guard is purely defensive.
    function getSectorFromTileId(tileId) {
        const id = parseInt(tileId, 10);
        if (isNaN(id)) return null;
        let data;
        try { data = SECTOR_DATA; } catch (e) { return null; }
        if (!data) return null;
        for (const name in data) {
            const sd = data[name];
            const end = sd.start + sd.cols * sd.rows - 1;
            if (id >= sd.start && id <= end) return name;
        }
        return null;
    }

    function getLocalCoordsFromTileId(tileId, sectorName) {
        const sd = getSectorData(sectorName);
        if (!sd) return null;
        const offset = parseInt(tileId, 10) - sd.start;
        if (offset < 0 || offset >= sd.cols * sd.rows) return null;
        return { x: Math.floor(offset / sd.rows), y: offset % sd.rows };
    }

    // Single-source Dijkstra: returns a { "x,y": apCost } map for every
    // reachable tile in the sector, starting from (startX, startY).  Runs
    // once instead of N times when we need distances to many targets.
    // Delegates to HPA* (hpaSectorAllDistances) which resolves the fragment
    // and runs the terrain-aware Dijkstra on the correct fragment grid.
    function getSectorAllDistances(sectorName, startX, startY) {
        const table = hpaGetTable();
        if (!table) return null;
        return hpaSectorAllDistances(table, sectorName, startX, startY);
    }

    // >> Wormhole seal calendar (ported from a third-party calculator)
    // The four wormholes (WH_A, WH_B, WH_C, WH_D) rotate on a
    // 2-day cycle.  Seal type A closes the current wormhole; seal type B closes
    // with a 3-day offset.  Returns a Set of lowercased sector names whose
    // wormhole is currently closed.
    function getWormholeSeals() {
        const seal = GM_getValue('config_ship_wormhole_seal', 'none');
        if (!seal || seal === 'none') return new Set();

        const epoch = 1449120361000; // December 3, 2015 05:26:01 GMT
        const days = (Date.now() - epoch) / 1000 / 60 / 60 / 24;
        const cycle = ['WH_A', 'WH_B', 'WH_C', 'WH_D'];
        const closed = new Set();

        switch (seal) {
            case 'seal_a':
            case 'seal_b':
                closed.add(cycle[Math.floor(days / 2) % 4]); break;
            case 'seal_c':
                closed.add(cycle[Math.floor((days + 3) / 2) % 4]); break;
            case 'wh-closed-A':    closed.add('WH_A'); break;
            case 'wh-closed-B':  closed.add('WH_B'); break;
            case 'wh-closed-C': closed.add('WH_C'); break;
            case 'wh-closed-D':  closed.add('WH_D'); break;
        }
        return closed;
    }

    // >> Cross-sector route builder (wormhole-aware)
    // Returns a multi-leg route from (fromSector, fromX, fromY) to
    // (toSector, toX, toY). Each leg is a local-sector path with tile IDs.
    // Wormhole jumps between legs are handled by the game automatically
    // (navigating onto a wormhole tile triggers the jump).
    //
    // Returns: { legs: [{ sector, path: [{x,y}...], tileIds: [...] }], totalAP }
    // or null if no route is found.
    // Delegates to HPA* (hpaFindRouteLegacy) which resolves fragments and
    // routes through the pre-compiled macro wormhole graph.
    function getCrossSectorRoute(fromSector, fromTileId, fromX, fromY, toSector, toX, toY) {
        const table = hpaGetTable();
        if (!table) return null;
        return hpaFindRouteLegacy(table, fromSector, { x: fromX, y: fromY }, toSector, { x: toX, y: toY });
    }

    // Fast cross-sector AP using the HPA* table.
    // Same-sector: direct Dijkstra lookup (with fragment resolution).
    // Cross-sector: min over (wh1 in fromSec, wh2 in toSec) of
    //   distFromA[wh1] + macroDist[wh1][wh2] + distFromWh2[dest]
    // Returns null if no route is found (NO estimate — hard-fail policy).
    // dijCache/macroGraph params are vestigial (HPA uses its own internal
    // cache) but kept for caller-signature compatibility.
    function getCrossSectorAPFast(fromCoords, fromSector, toCoords, toSector, dijCache, macroGraph) {
        if (!fromCoords || !toCoords || !fromSector || !toSector) {
            throw new Error('getCrossSectorAPFast: null coords or sector (from=' + fromSector + '/' + JSON.stringify(fromCoords) + ', to=' + toSector + '/' + JSON.stringify(toCoords) + ')');
        }
        const table = hpaGetTable();
        if (!table) return null;
        const ap = hpaCrossSectorAP(table, fromSector, fromCoords, toSector, toCoords);
        return (ap !== null && isFinite(ap)) ? ap : null;
    }
    // --- 14.5. HPA* equip_f ---

    // >> Design overview
    // Two-tier pathfinding that replaces the brute-force cross-sector Dijkstra
    // in part 14/19 with a pre-compiled hierarchical graph:
    //
    //   Macro graph: wormhole tiles as nodes. Edges = wormhole jumps (cost =
    //     wjump) + intra-sector Dijkstra distances (recomputed with the
    //     caller-supplied terrainAP, NOT the vanilla matrices in map_data).
    //     All-pairs shortest path via Floyd-Warshall. Cached per seal-cycle.
    //
    //   Micro graph: local A* within a single sector grid fragment. Only
    //     runs for: start → first exit wormhole, last entry wormhole → dest.
    //
    // Fragmentation: map_data.txt sub-sectors (Fragment-A, Fragment-0
    //   West, Core West, Core NE, etc.) are kept as SEPARATE clusters.
    //   No grid merging. Wormholes in different fragments of the same nominal
    //   sector have no intra-sector edge — the macro graph routes around them
    //   via other sectors. This structurally eliminates the Fragment-0
    //   split-sector routing bug without hardcoding sector names.
    //
    // Padding: grids are padded to SECTOR_DATA dimensions with 'b' (blocked),
    //   never 'f' (type_a). This fixes the Sector-X nook bug where phantom
    //   type_a tiles in padded rows created false paths around the flask-shaped
    //   wall at [27,33].
    //
    // AP accuracy: the pre-computed wormhole matrices in map_data.txt
    //   (e.g. "226/19 167/14") use vanilla terrain costs (f=11, e=20, etc.)
    //   and ignore ship equipment (drive speed, nav level, equip_f, boost,
    //   stim, equip_b/equip_c, equip_d). Non-uniform terrain means
    //   you cannot scale them by a ratio. This module ignores them entirely
    //   and recomputes all intra-sector wormhole distances via Dijkstra with
    //   the caller-supplied terrainAP table (output of computeTileCosts()).
    //
    // Purity: all core functions below are pure — no closures over IIFE
    //   globals (no GM_*, no parsedMap, no SECTOR_DATA). Every dependency is
    //   passed as an argument. Compile is synchronous via hpaGetTable()
    //   (lazy, cached by terrainAP|wjump|sealed key).
    //
    // Hard-fail policy: unknown sector → throw. Unreachable target → null.
    //   No Manhattan/Chebyshev estimate fallbacks (per AGENTS.md).

    // >> Name resolver — resolves sub-sector/alternate-name lookups to their
    // canonical SECTOR_DATA key. Ports _resolveSectorName from part 01.
    function hpaResolveSectorName(name, sectorMeta) {
        if (!name || !sectorMeta) return null;
        if (sectorMeta[name]) return sectorMeta[name];
        const parent = name.replace(/ (East|West|North|South|Inner|NE|SE|NW|SW)$/, '');
        if (parent !== name && sectorMeta[parent]) return sectorMeta[parent];
        const spaced = name.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
        if (spaced !== name && sectorMeta[spaced]) return sectorMeta[spaced];
        const parentSpaced = parent.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
        if (parentSpaced !== parent && sectorMeta[parentSpaced]) return sectorMeta[parentSpaced];
        return null;
    }

    // >> Canonical NAME resolver — returns the canonical SECTOR_DATA key STRING
    // (e.g. "Fragment-0" for the fragment "Fragment-A"), or null. Unlike
    // hpaResolveSectorName() above — which returns the data ENTRY object
    // ({start,cols,rows}) — this returns the NAME so callers can key external
    // maps whose keys are canonical sector-name strings (e.g. the live-terrain
    // store populated by scrapeAndStoreTerrain in part 15). Pure: takes
    // sectorMeta as an argument, no closure over IIFE globals.
    function hpaResolveSectorNameKey(name, sectorMeta) {
        if (!name || !sectorMeta) return null;
        if (sectorMeta[name]) return name;
        const parent = name.replace(/ (East|West|North|South|Inner|NE|SE|NW|SW)$/, '');
        if (parent !== name && sectorMeta[parent]) return parent;
        const spaced = name.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
        if (spaced !== name && sectorMeta[spaced]) return spaced;
        const parentSpaced = parent.replace(/^([A-Za-z.-]+)(\d)/, '$1 $2');
        if (parentSpaced !== parent && sectorMeta[parentSpaced]) return parentSpaced;
        return null;
    }

    // >> Fragment resolver — given a canonical sector name + (x,y), find which
    // parsed fragment actually contains that tile (non-'b'). This is the key
    // to handling Fragment-0: "Fragment-0" + (5,10) → "Fragment-B",
    // "Fragment-0" + (30,1) → "Fragment-A". If the tile is 'b' in all
    // fragments, the first fragment is returned (A*/Dijkstra will return null
    // for blocked tiles, which is correct behavior).
    function hpaResolveFragment(sectors, canonicalName, x, y) {
        if (sectors.has(canonicalName)) return canonicalName;
        const dirs = ['East', 'West', 'North', 'South', 'Inner', 'NE', 'SE', 'NW', 'SW'];
        for (const dir of dirs) {
            const fragName = canonicalName + ' ' + dir;
            if (!sectors.has(fragName)) continue;
            const sec = sectors.get(fragName);
            if (sec.grid.length === 0) continue;
            if (y >= 0 && y < sec.grid.length && x >= 0 && x < sec.grid[0].length && sec.grid[y][x] !== 'b') {
                return fragName;
            }
        }
        for (const dir of dirs) {
            const fragName = canonicalName + ' ' + dir;
            if (sectors.has(fragName)) return fragName;
        }
        return canonicalName;
    }

    // >> Wormhole pairing — match source wormholes to destination wormholes
    // by #sub-region suffix (e.g. SectorA#West <-> SectorA#West). Falls back
    // to 1:1 when both sides have exactly one entry and no suffix.
    function hpaPairWormholes(fromList, toList) {
        const pairs = [];
        for (const fw of fromList) {
            let tw = toList.find(t => t.sub === fw.sub);
            if (!tw && fromList.length === 1 && toList.length === 1) tw = toList[0];
            if (!tw) continue;
            pairs.push({ from: fw, to: tw });
        }
        return pairs;
    }

    // >> Parser — parse map_data.txt into separate sector fragments.
    // NO merging. Each `sector Name:cols,rows` block becomes one entry in
    // the returned Map. Grids are padded to SECTOR_DATA dimensions with 'b'.
    function hpaParseMap(rawText, sectorMeta, liveTerrain) {
        const sectors = new Map();
        const lines = rawText.split(/[\r\n]+/);
        let cur = null;

        for (let line of lines) {
            line = line.trim();
            if (!line) continue;

            if (line.startsWith('sector ')) {
                const parts = line.substring(7).split(':');
                cur = parts[0].replace(/_/g, ' ');
                sectors.set(cur, { name: cur, grid: [], wormholes: [], beacons: [] });
            } else if (line.startsWith('wh ') && cur) {
                const parts = line.split(/\s+/);
                let dest = parts[1].replace(/_/g, ' ');
                const hashIdx = dest.indexOf('#');
                let sub = null;
                if (hashIdx >= 0) {
                    sub = dest.substring(hashIdx + 1);
                    dest = dest.substring(0, hashIdx);
                }
                const x = parseInt(parts[2], 10);
                const y = parseInt(parts[3], 10);
                const matrices = [];
                for (let i = 4; i < parts.length; i++) {
                    const m = parts[i].match(/^(\d+)\/(\d+)$/);
                    if (m) matrices.push({ ap: +m[1], type_a: +m[2] });
                }
                sectors.get(cur).wormholes.push({ dest, x, y, sub, matrices });
            } else if (line.startsWith('beacon ') && cur) {
                const parts = line.split(/\s+/);
                sectors.get(cur).beacons.push({
                    x: parseInt(parts[parts.length - 2], 10),
                    y: parseInt(parts[parts.length - 1], 10),
                });
            } else if (cur && /^\S{4,}$/.test(line) && !/^(sector|wh|beacon|station)\b/i.test(line)) {
                sectors.get(cur).grid.push(line.toLowerCase().split(''));
            }
        }

        // Pad grids to SECTOR_DATA dimensions with 'b' (blocked, NEVER 'f').
        // This fixes the Sector-X nook bug where padded 'f' rows created
        // phantom type_a tiles around the flask-shaped wall at [27,33].
        for (const [name, sec] of sectors) {
            if (sec.grid.length === 0) continue;
            const meta = hpaResolveSectorName(name, sectorMeta);
            if (!meta) continue;
            const tRows = meta.rows;
            const tCols = meta.cols;
            while (sec.grid.length < tRows) sec.grid.push(new Array(tCols).fill('b'));
            for (const row of sec.grid) {
                while (row.length < tCols) row.push('b');
            }
        }

        // >> Live-terrain overlay — runs AFTER padding so live tiles overwrite
        // padded 'b' rows (e.g. Sector-X y=38,39), and BEFORE return. Live
        // terrain is ground truth and always wins over map_data values.
        // Passed in from hpaGetTable() (the IIFE bridge) to keep hpaParseMap
        // pure — no GM_* here. Keys are canonical sector-name strings, resolved
        // via hpaResolveSectorNameKey so fragment names (e.g. "Fragment-0
        // East") match their canonical store key ("Fragment-0").
        if (liveTerrain) {
            for (const [name, sec] of sectors) {
                if (sec.grid.length === 0) continue;
                const canonical = hpaResolveSectorNameKey(name, sectorMeta);
                if (!canonical) continue;
                const live = liveTerrain[canonical];
                if (!live) continue;
                for (const [key, char] of Object.entries(live)) {
                    const parts = key.split(',');
                    const x = +parts[0], y = +parts[1];
                    if (y >= 0 && y < sec.grid.length && x >= 0 && x < sec.grid[0].length) {
                        sec.grid[y][x] = char;
                    }
                }
            }
        }

        return sectors;
    }

    // >> Binary min-heap for Dijkstra/A* priority queues. O(log n) push/pop
    // vs O(n log n) array sort. Critical for compile time: hpaBuildMacroGraph
    // runs 1104 Dijkstra calls; each with up to ~1000 nodes in the open set.
    function _hpaBinHeap(cmp) {
        const a = [];
        return {
            get length() { return a.length; },
            push(v) {
                a.push(v);
                let i = a.length - 1;
                while (i > 0) {
                    const p = (i - 1) >> 1;
                    if (cmp(a[p], a[i]) <= 0) break;
                    const t = a[p]; a[p] = a[i]; a[i] = t; i = p;
                }
            },
            shift() {
                if (a.length === 0) return undefined;
                const top = a[0];
                const last = a.pop();
                if (a.length > 0) {
                    a[0] = last;
                    let i = 0;
                    const n = a.length;
                    while (true) {
                        let l = 2 * i + 1, r = 2 * i + 2, m = i;
                        if (l < n && cmp(a[l], a[m]) < 0) m = l;
                        if (r < n && cmp(a[r], a[m]) < 0) m = r;
                        if (m === i) break;
                        const t = a[m]; a[m] = a[i]; a[i] = t; i = m;
                    }
                }
                return top;
            }
        };
    }

    // >> Single-source Dijkstra over a sector grid.
    // Returns a Map<"x,y", apCost> for every reachable tile. the terrain
    // is ASYMMETRIC: entering a tile costs that tile's terrainAP, so a
    // Dijkstra FROM X gives distances FROM X (not TH X). To get distance TH
    // a destination, run Dijkstra FROM the source you're measuring from.
    function hpaLocalDijkstra(grid, terrainAP, sx, sy) {
        const rows = grid.length;
        if (rows === 0) return null;
        const cols = grid[0].length;
        if (sx < 0 || sy < 0 || sx >= cols || sy >= rows) return null;

        const dist = new Map();
        const pq = _hpaBinHeap((a, b) => a.cost - b.cost);
        dist.set(sx + ',' + sy, 0);
        pq.push({ x: sx, y: sy, cost: 0 });

        while (pq.length > 0) {
            const cur = pq.shift();
            const cKey = cur.x + ',' + cur.y;
            if (cur.cost > dist.get(cKey)) continue;

            for (let dy = -1; dy <= 1; dy++) {
                for (let dx = -1; dx <= 1; dx++) {
                    if (dx === 0 && dy === 0) continue;
                    const nx = cur.x + dx, ny = cur.y + dy;
                    if (nx < 0 || ny < 0 || nx >= cols || ny >= rows) continue;
                    const terrain = grid[ny][nx];
                    const moveCost = terrainAP[terrain];
                    if (moveCost === undefined || !isFinite(moveCost)) continue;
                    const newCost = cur.cost + moveCost;
                    const nKey = nx + ',' + ny;
                    if (!dist.has(nKey) || newCost < dist.get(nKey)) {
                        dist.set(nKey, newCost);
                        pq.push({ x: nx, y: ny, cost: newCost });
                    }
                }
            }
        }
        return dist;
    }

    // >> Local A* with turn-minimization tiebreaker.
    // Heuristic: Chebyshev distance × min terrain cost (admissible — diagonal
    // moves cost the same as orthogonal in the game, and min cost is a lower
    // bound on per-tile cost). Turn minimization produces straighter paths,
    // which lets the flight loop extend each click to the full nav range.
    function hpaLocalAStar(grid, terrainAP, sx, sy, ex, ey) {
        const rows = grid.length;
        if (rows === 0) return null;
        const cols = grid[0].length;
        if (sx < 0 || sy < 0 || sx >= cols || sy >= rows) return null;
        if (ex < 0 || ey < 0 || ex >= cols || ey >= rows) return null;

        let minCost = Infinity;
        for (const v of Object.values(terrainAP)) {
            if (isFinite(v) && v < minCost) minCost = v;
        }

        const gScore = new Map();
        const turns = new Map();
        const prev = new Map();
        const open = _hpaBinHeap((a, b) => (a.f - b.f) || (a.t - b.t));

        const startKey = sx + ',' + sy;
        gScore.set(startKey, 0);
        turns.set(startKey, 0);
        open.push({
            x: sx, y: sy, g: 0, t: 0, dir: null,
            f: Math.max(Math.abs(sx - ex), Math.abs(sy - ey)) * minCost
        });

        while (open.length > 0) {
            const cur = open.shift();
            const cKey = cur.x + ',' + cur.y;
            if (cur.g > gScore.get(cKey)) continue;
            if (cur.x === ex && cur.y === ey) break;

            for (let dy = -1; dy <= 1; dy++) {
                for (let dx = -1; dx <= 1; dx++) {
                    if (dx === 0 && dy === 0) continue;
                    const nx = cur.x + dx, ny = cur.y + dy;
                    if (nx < 0 || ny < 0 || nx >= cols || ny >= rows) continue;
                    const terrain = grid[ny][nx];
                    const moveCost = terrainAP[terrain];
                    if (moveCost === undefined || !isFinite(moveCost)) continue;
                    const nKey = nx + ',' + ny;
                    const tentativeG = cur.g + moveCost;
                    const dirKey = dx + ',' + dy;
                    const newTurns = (cur.dir && cur.dir !== dirKey) ? cur.t + 1 : cur.t;
                    const existingG = gScore.get(nKey);
                    if (existingG === undefined || tentativeG < existingG ||
                        (tentativeG === existingG && newTurns < turns.get(nKey))) {
                        gScore.set(nKey, tentativeG);
                        turns.set(nKey, newTurns);
                        prev.set(nKey, cKey);
                        const h = Math.max(Math.abs(nx - ex), Math.abs(ny - ey)) * minCost;
                        open.push({ x: nx, y: ny, g: tentativeG, t: newTurns, dir: dirKey, f: tentativeG + h });
                    }
                }
            }
        }

        const endKey = ex + ',' + ey;
        if (!gScore.has(endKey)) return null;

        const path = [];
        let cur = endKey;
        while (cur) {
            const [px, py] = cur.split(',').map(Number);
            path.unshift({ x: px, y: py });
            cur = prev.get(cur);
        }
        return path;
    }

    // >> Macro graph builder — Floyd-Warshall over wormhole tiles.
    // Nodes = wormhole tiles (keyed "sector|x,y"). Edges = wormhole jumps
    // (directed, cost=wjump) + intra-sector Dijkstra distances (directed,
    // cost=A* path cost). Sealed sectors' wormholes are excluded.
    // Returns { nodes, distFlat, nextFlat, keyToIdx, wormholesBySector, nodeCount }.
    function hpaBuildMacroGraph(sectors, terrainAP, wjump, sealed) {
        const nodes = [];
        const nodeSet = new Set();
        const jumpEdges = [];

        for (const [secName, sec] of sectors) {
            if (!sec.wormholes || sec.wormholes.length === 0) continue;
            const byDest = new Map();
            for (const wh of sec.wormholes) {
                if (!byDest.has(wh.dest)) byDest.set(wh.dest, []);
                byDest.get(wh.dest).push(wh);
            }
            for (const [destName, fromList] of byDest) {
                if (sealed.has(secName.toLowerCase()) || sealed.has(destName.toLowerCase())) continue;
                const destSec = sectors.get(destName);
                if (!destSec || !destSec.wormholes) continue;
                const toList = destSec.wormholes.filter(w => w.dest === secName);
                if (toList.length === 0) continue;
                for (const pair of hpaPairWormholes(fromList, toList)) {
                    const fromKey = secName + '|' + pair.from.x + ',' + pair.from.y;
                    const toKey = destName + '|' + pair.to.x + ',' + pair.to.y;
                    if (!nodeSet.has(fromKey)) {
                        nodeSet.add(fromKey);
                        nodes.push({ key: fromKey, sec: secName, x: pair.from.x, y: pair.from.y });
                    }
                    if (!nodeSet.has(toKey)) {
                        nodeSet.add(toKey);
                        nodes.push({ key: toKey, sec: destName, x: pair.to.x, y: pair.to.y });
                    }
                    jumpEdges.push({ from: fromKey, to: toKey, cost: wjump });
                }
            }
        }

        if (nodes.length === 0) {
            return { nodes, distFlat: new Int16Array(0), nextFlat: new Int16Array(0), keyToIdx: new Map(), wormholesBySector: new Map(), nodeCount: 0 };
        }

        const nodesBySector = new Map();
        for (const n of nodes) {
            if (!nodesBySector.has(n.sec)) nodesBySector.set(n.sec, []);
            nodesBySector.get(n.sec).push(n);
        }

        // Intra-sector directed edges via Dijkstra from each wormhole tile.
        const intraEdges = [];
        for (const [secName, secNodes] of nodesBySector) {
            const sec = sectors.get(secName);
            if (!sec || sec.grid.length === 0) continue;
            for (const src of secNodes) {
                const dist = hpaLocalDijkstra(sec.grid, terrainAP, src.x, src.y);
                if (!dist) continue;
                for (const dst of secNodes) {
                    if (src.key === dst.key) continue;
                    const d = dist.get(dst.x + ',' + dst.y);
                    if (d !== undefined && isFinite(d)) {
                        intraEdges.push({ from: src.key, to: dst.key, cost: d });
                    }
                }
            }
        }

        // Floyd-Warshall on directed graph.
        const n = nodes.length;
        const idx = new Map();
        nodes.forEach((node, i) => idx.set(node.key, i));

        const dist = new Float64Array(n * n);
        const next = new Int32Array(n * n);
        dist.fill(Infinity);
        next.fill(-1);
        for (let i = 0; i < n; i++) {
            dist[i * n + i] = 0;
            next[i * n + i] = i;
        }
        for (const e of jumpEdges) {
            const i = idx.get(e.from), j = idx.get(e.to);
            if (i != null && j != null && e.cost < dist[i * n + j]) {
                dist[i * n + j] = e.cost;
                next[i * n + j] = j;
            }
        }
        for (const e of intraEdges) {
            const i = idx.get(e.from), j = idx.get(e.to);
            if (i != null && j != null && e.cost < dist[i * n + j]) {
                dist[i * n + j] = e.cost;
                next[i * n + j] = j;
            }
        }
        for (let k = 0; k < n; k++) {
            for (let i = 0; i < n; i++) {
                const dik = dist[i * n + k];
                if (dik === Infinity) continue;
                const ik = i * n; const kj = k * n;
                for (let j = 0; j < n; j++) {
                    const alt = dik + dist[kj + j];
                    if (alt < dist[ik + j]) {
                        dist[ik + j] = alt;
                        next[ik + j] = next[ik + k];
                    }
                }
            }
        }

        // Flatten dist/next to Int16Array (primary representation for queries + serialize).
        const distFlat = new Int16Array(n * n);
        const nextFlat = new Int16Array(n * n);
        for (let i = 0; i < n; i++) {
            for (let j = 0; j < n; j++) {
                const d = dist[i * n + j];
                distFlat[i * n + j] = isFinite(d) ? d : -1;
                const nx = next[i * n + j];
                nextFlat[i * n + j] = (nx !== -1 && nx !== undefined) ? nx : -1;
            }
        }

        const keyToIdx = new Map();
        nodes.forEach((nd, i) => keyToIdx.set(nd.key, i));

        return { nodes, distFlat, nextFlat, keyToIdx, wormholesBySector: nodesBySector, nodeCount: n };
    }

    // >> Compile — one-time build. Pure function (no IIFE globals).
    // Called synchronously by hpaGetTable() on first query.
    // Returns a table with Map/Set (structured-clone safe if ever offloaded).
    function hpaCompile(rawText, sectorMeta, terrainAP, wjump, sealed, liveTerrain) {
        __setOp('hpaCompile');
        const sectors = hpaParseMap(rawText, sectorMeta, liveTerrain);
        const macro = hpaBuildMacroGraph(sectors, terrainAP, wjump || 10, sealed || new Set());
        return { sectors, macro, terrainAP, wjump: wjump || 10, dijCache: new Map() };
    }

    // >> Persistence schema version — bump when serialize format changes.
    const HPA_MACRO_SCHEMA = 2;

    // >> Base64 helpers for typed array serialization (chunked to avoid
    // call-stack limits on large arrays).
    function hpaBytesToBase64(bytes) {
        let binary = '';
        const chunk = 8192;
        for (let i = 0; i < bytes.length; i += chunk) {
            binary += String.fromCharCode.apply(null, bytes.subarray(i, i + chunk));
        }
        return btoa(binary);
    }

    function hpaBase64ToBytes(b64) {
        const binary = atob(b64);
        const bytes = new Uint8Array(binary.length);
        for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
        return bytes;
    }

    // >> Serialize the HPA* table to a JSON string for GM_setValue.
    // distFlat/nextFlat are already Int16Array — base64-encode directly.
    // ~6 MB — under GM_setValue's practical ~10 MB storage limit.
    function hpaSerializeTable(table, cacheKey) {
        const n = table.macro.nodeCount;
        const nodes = table.macro.nodes;
        const distFlat = table.macro.distFlat;
        const nextFlat = table.macro.nextFlat;

        const distB64 = hpaBytesToBase64(new Uint8Array(distFlat.buffer));
        const nextB64 = hpaBytesToBase64(new Uint8Array(nextFlat.buffer));

        const wbArr = [];
        for (const [k, v] of table.macro.wormholesBySector) {
            wbArr.push([k, v.map(nd => [nd.key, nd.sec, nd.x, nd.y])]);
        }

        const dijArr = [];
        for (const [k, v] of table.dijCache) {
            dijArr.push([k, [...v.entries()]]);
        }

        return JSON.stringify({
            schema: HPA_MACRO_SCHEMA,
            key: cacheKey,
            n: n,
            nodes: nodes.map(nd => [nd.key, nd.sec, nd.x, nd.y]),
            dist: distB64,
            next: nextB64,
            wormholesBySector: wbArr,
            wjump: table.wjump,
            dijCache: dijArr,
        });
    }

    // >> Deserialize the HPA* table from a GM_getValue JSON string.
    // Creates Int16Array views on the decoded base64 buffers (zero-copy),
    // builds a 1104-entry keyToIdx Map, and re-parses sector grids from
    // rawText (cheap — no Dijkstra/Floyd-Warshall). No Map-of-Maps rebuild.
    // terrainAP is passed in (not deserialized) because JSON.stringify
    // converts Infinity → null, which would make impassable tiles passable.
    // Returns null when schema or cacheKey doesn't match.
    function hpaDeserializeTable(storedJson, expectedKey, rawText, sectorMeta, terrainAP, liveTerrain) {
        const stored = JSON.parse(storedJson);
        if (stored.schema !== HPA_MACRO_SCHEMA) return null;
        if (stored.key !== expectedKey) return null;

        const n = stored.n;
        const nodes = stored.nodes.map(nd => ({ key: nd[0], sec: nd[1], x: nd[2], y: nd[3] }));

        const distBytes = hpaBase64ToBytes(stored.dist);
        const nextBytes = hpaBase64ToBytes(stored.next);
        const distFlat = new Int16Array(distBytes.buffer);
        const nextFlat = new Int16Array(nextBytes.buffer);

        const keyToIdx = new Map();
        nodes.forEach((nd, i) => keyToIdx.set(nd.key, i));

        const wormholesBySector = new Map();
        for (const [k, v] of stored.wormholesBySector) {
            wormholesBySector.set(k, v.map(nd => ({ key: nd[0], sec: nd[1], x: nd[2], y: nd[3] })));
        }

        const dijCache = new Map();
        if (stored.dijCache) {
            for (const [k, entries] of stored.dijCache) {
                dijCache.set(k, new Map(entries));
            }
        }

        const sectors = hpaParseMap(rawText, sectorMeta, liveTerrain);

        return {
            sectors: sectors,
            macro: { nodes, distFlat, nextFlat, keyToIdx, wormholesBySector, nodeCount: n },
            terrainAP: terrainAP,
            wjump: stored.wjump,
            dijCache: dijCache,
        };
    }

    // >> Cached local Dijkstra — avoids recomputing for the same (sector, tile).
    function hpaLocalDijkstraCached(table, secName, x, y) {
        const key = secName + '|' + x + ',' + y;
        if (table.dijCache.has(key)) return table.dijCache.get(key);
        const sec = table.sectors.get(secName);
        if (!sec) return null;
        const dist = hpaLocalDijkstra(sec.grid, table.terrainAP, x, y);
        table.dijCache.set(key, dist);
        return dist;
    }

    // >> Fast cross-sector AP query — no path reconstruction.
    // Same sector: single Dijkstra lookup.
    // Cross-sector: min over (wh1 in fromSec, wh2 in toSec) of
    //   distFromStart[wh1] + macroDist[wh1][wh2] + distFromWh2[dest]
    // Terrain is asymmetric, so distFromWh2 is Dijkstra FROM wh2 (gives
    // distances FROM wh2, including TH dest).
    // Returns null if unreachable. Throws if sector not in map.
    function hpaCrossSectorAP(table, fromSec, fromXY, toSec, toXY) {
        if (!fromSec || !toSec) {
            throw new Error('hpaCrossSectorAP: sector unknown (from=' + fromSec + ', to=' + toSec + ')');
        }

        fromSec = hpaResolveFragment(table.sectors, fromSec, fromXY.x, fromXY.y);
        toSec = hpaResolveFragment(table.sectors, toSec, toXY.x, toXY.y);

        if (!table.sectors.has(fromSec)) {
            throw new Error('hpaCrossSectorAP: sector not in map: ' + fromSec);
        }
        if (!table.sectors.has(toSec)) {
            throw new Error('hpaCrossSectorAP: sector not in map: ' + toSec);
        }

        if (fromSec === toSec) {
            const dist = hpaLocalDijkstraCached(table, fromSec, fromXY.x, fromXY.y);
            if (!dist) return null;
            const v = dist.get(toXY.x + ',' + toXY.y);
            return (v !== undefined && isFinite(v)) ? v : null;
        }

        const fromWhs = table.macro.wormholesBySector.get(fromSec);
        const toWhs = table.macro.wormholesBySector.get(toSec);
        if (!fromWhs || !toWhs) return null;

        const fromDist = hpaLocalDijkstraCached(table, fromSec, fromXY.x, fromXY.y);
        if (!fromDist) return null;

        const distFlat = table.macro.distFlat;
        const keyToIdx = table.macro.keyToIdx;
        const n = table.macro.nodeCount;
        let best = Infinity;
        for (const w1 of fromWhs) {
            const d1 = fromDist.get(w1.x + ',' + w1.y);
            if (d1 === undefined || !isFinite(d1)) continue;
            const i1 = keyToIdx.get(w1.key);
            if (i1 === undefined) continue;
            for (const w2 of toWhs) {
                const i2 = keyToIdx.get(w2.key);
                if (i2 === undefined) continue;
                const macroLeg = distFlat[i1 * n + i2];
                if (macroLeg < 0) continue;
                const toDist = hpaLocalDijkstraCached(table, toSec, w2.x, w2.y);
                if (!toDist) continue;
                const d2 = toDist.get(toXY.x + ',' + toXY.y);
                if (d2 === undefined || !isFinite(d2)) continue;
                const total = d1 + macroLeg + d2;
                if (total < best) best = total;
            }
        }
        return isFinite(best) ? best : null;
    }

    // >> Full route with path reconstruction — HPA* hand-off.
    // 1. Find optimal (w1, w2) pair via the same formula as hpaCrossSectorAP.
    // 2. Reconstruct macro wormhole sequence via nextFlat (Floyd-Warshall
    //    next-hop chain).
    // 3. Build legs: local A* for each intra-sector segment between
    //    consecutive wormhole tiles in the same sector. Wormhole jumps
    //    are implicit (between legs).
    // 4. Total AP = sum of leg AP costs + wjump × (number of jumps).
    // Returns { legs: [{sector, path: [{x,y}...]}], totalAP } or null.
    function hpaFindRoute(table, fromSec, fromXY, toSec, toXY) {
        if (!fromSec || !toSec) {
            throw new Error('hpaFindRoute: sector unknown (from=' + fromSec + ', to=' + toSec + ')');
        }

        fromSec = hpaResolveFragment(table.sectors, fromSec, fromXY.x, fromXY.y);
        toSec = hpaResolveFragment(table.sectors, toSec, toXY.x, toXY.y);

        if (!table.sectors.has(fromSec)) {
            throw new Error('hpaFindRoute: sector not in map: ' + fromSec);
        }
        if (!table.sectors.has(toSec)) {
            throw new Error('hpaFindRoute: sector not in map: ' + toSec);
        }

        const fromSecData = table.sectors.get(fromSec);
        const toSecData = table.sectors.get(toSec);

        // Same sector — single A* leg.
        if (fromSec === toSec) {
            const path = hpaLocalAStar(toSecData.grid, table.terrainAP, fromXY.x, fromXY.y, toXY.x, toXY.y);
            if (!path) return null;
            let ap = 0;
            for (let i = 1; i < path.length; i++) {
                ap += table.terrainAP[toSecData.grid[path[i].y][path[i].x]];
            }
            return { legs: [{ sector: fromSec, path }], totalAP: ap };
        }

        const fromWhs = table.macro.wormholesBySector.get(fromSec);
        const toWhs = table.macro.wormholesBySector.get(toSec);
        if (!fromWhs || !toWhs) return null;

        const fromDist = hpaLocalDijkstraCached(table, fromSec, fromXY.x, fromXY.y);
        if (!fromDist) return null;

        // Find optimal (w1, w2) pair.
        const distFlat = table.macro.distFlat;
        const keyToIdx = table.macro.keyToIdx;
        const n = table.macro.nodeCount;
        let bestPair = null;
        for (const w1 of fromWhs) {
            const d1 = fromDist.get(w1.x + ',' + w1.y);
            if (d1 === undefined || !isFinite(d1)) continue;
            const i1 = keyToIdx.get(w1.key);
            if (i1 === undefined) continue;
            for (const w2 of toWhs) {
                const i2 = keyToIdx.get(w2.key);
                if (i2 === undefined) continue;
                const macroLeg = distFlat[i1 * n + i2];
                if (macroLeg < 0) continue;
                const toDist = hpaLocalDijkstraCached(table, toSec, w2.x, w2.y);
                if (!toDist) continue;
                const d2 = toDist.get(toXY.x + ',' + toXY.y);
                if (d2 === undefined || !isFinite(d2)) continue;
                const total = d1 + macroLeg + d2;
                if (!bestPair || total < bestPair.total) {
                    bestPair = { w1, w2, total };
                }
            }
        }
        if (!bestPair) return null;

        // Reconstruct macro wormhole sequence via nextFlat (index space).
        const nextFlat = table.macro.nextFlat;
        const macroNodes = table.macro.nodes;
        const targetIdx = keyToIdx.get(bestPair.w2.key);
        const macroPath = [bestPair.w1.key];
        let curIdx = keyToIdx.get(bestPair.w1.key);
        let guard = 0;
        while (curIdx !== targetIdx && guard++ < 500) {
            const nextIdx = nextFlat[curIdx * n + targetIdx];
            if (nextIdx < 0 || nextIdx >= n) return null;
            macroPath.push(macroNodes[nextIdx].key);
            curIdx = nextIdx;
        }
        if (curIdx !== targetIdx) return null;

        // Parse macro path nodes into {sec, x, y}.
        const parsedPath = macroPath.map(k => {
            const [sec, coords] = k.split('|');
            const [x, y] = coords.split(',').map(Number);
            return { sec, x, y };
        });

        // Build legs: A* for each intra-sector segment, skip wormhole jumps.
        // Degenerate legs (single-tile, already at wormhole) are emitted so
        // callers see the full sector sequence and wjump count stays correct.
        const legs = [];
        let curPos = { sec: fromSec, x: fromXY.x, y: fromXY.y };

        for (const node of parsedPath) {
            if (node.sec === curPos.sec) {
                if (node.x === curPos.x && node.y === curPos.y) {
                    legs.push({ sector: curPos.sec, path: [{ x: curPos.x, y: curPos.y }] });
                } else {
                    const sec = table.sectors.get(curPos.sec);
                    const path = hpaLocalAStar(sec.grid, table.terrainAP, curPos.x, curPos.y, node.x, node.y);
                    if (!path) return null;
                    legs.push({ sector: curPos.sec, path });
                }
            }
            curPos = { sec: node.sec, x: node.x, y: node.y };
        }

        // Final leg: from last wormhole to destination.
        const finalSec = table.sectors.get(curPos.sec);
        const finalPath = hpaLocalAStar(finalSec.grid, table.terrainAP, curPos.x, curPos.y, toXY.x, toXY.y);
        if (!finalPath) return null;
        legs.push({ sector: curPos.sec, path: finalPath });

        // Total AP = leg terrain costs + wjump per wormhole jump.
        // Jump count comes from the macro path (sector transitions), NOT
        // from legs.length — degenerate legs occupy a slot but don't jump.
        let numJumps = 0;
        for (let i = 1; i < parsedPath.length; i++) {
            if (parsedPath[i].sec !== parsedPath[i - 1].sec) numJumps++;
        }
        let totalAP = 0;
        for (const leg of legs) {
            const grid = table.sectors.get(leg.sector).grid;
            for (let j = 1; j < leg.path.length; j++) {
                totalAP += table.terrainAP[grid[leg.path[j].y][leg.path[j].x]];
            }
        }
        totalAP += numJumps * table.wjump;

        return { legs, totalAP };
    }

    // >> Lazy-compile cache — bridges the pure HPA* core to the IIFE.
    // Compiles on first query, cached by terrainAP+wjump+sealed key so it
    // auto-invalidates when ship config or wormhole seals change.
    // Persists the compiled macro graph to GM_setValue so subsequent page
    // loads skip the ~5s Dijkstra+Floyd-Warshall compile. Falls back to full
    // compile (with a console.warn) when the stored data is missing, stale,
    // corrupt, or when GM_setValue quota is exceeded.
    let _hpaTable = null, _hpaTableKey = null;
    function hpaGetTable() {
        __setOp('hpaGetTable');
        const __tEntry = __perfOn ? performance.now() : 0;
        try {
            const rawText = localStorage.getItem("logistics_static_map_data");
            if (!rawText || rawText.includes("PASTE_YOUR_STATICXT_TXT_HERE")) return null;
            // Live terrain scraped from nav pages (part 15). Ground truth over
            // map_data; version increments only when a NEW tile is discovered,
            // which invalidates the macro-graph cache via the cache key below.
            const liveTerrain = GM_getValue('logistics_terrain_v1', {});
            const terrainVersion = GM_getValue('logistics_terrain_version', 0);
            const terrainAP = getTerrainAP();
            const shipOpt = getShipOptions();
            const wjump = Number(shipOpt.wormhole_cost) || 10;
            let sealed;
            try { sealed = getWormholeSeals(); } catch (e) { sealed = new Set(); }
            const key = JSON.stringify(terrainAP) + '|' + wjump + '|' + [...sealed].sort().join(',')
                        + '|' + rawText.length + '|' + HPA_MACRO_SCHEMA + '|' + terrainVersion;
            if (_hpaTableKey === key && _hpaTable) { __heavyT1('hpaL1', __tEntry); return _hpaTable; }

            // L1: top-window cache. The frameset (top) survives main-frame
            // reloads, so a JS object reference here skips the ~500ms-2s
            // GM_setValue deserialize on every ~5s full refresh. Wrap in
            // try/catch — cross-origin or no frameset silently falls through
            // to L2 (this is the expected fallback, not an error).
            try {
                if (top.__hpaTableKey === key && top.__hpaTable) {
                    _hpaTable = top.__hpaTable;
                    _hpaTableKey = key;
                    __heavyT1('hpaL1', __tEntry);
                    return top.__hpaTable;
                }
            } catch (e) { /* no top cache — fall through to L2 */ }

            // Try persistent cache (GM_setValue from a previous page load).
            const storedJson = GM_getValue('logistics_hpa_macro_v1', null);
            console.log('[hpa] L2: ' + (storedJson ? (storedJson.length / 1024 / 1024).toFixed(1) + ' MB retrieved' : 'null (no persisted data)'));
            if (storedJson) {
                try {
                    const table = hpaDeserializeTable(storedJson, key, rawText, SECTOR_DATA, terrainAP, liveTerrain);
                    if (table && table.macro.nodeCount > 0) {
                        console.log('[hpa] L2: deserialize OK (nodeCount=' + table.macro.nodeCount + ')');
                        _hpaTable = table;
                        _hpaTableKey = key;
                        try {
                            top.__hpaTable = table;
                            top.__hpaTableKey = key;
                            top.__hpaTerrainAP = terrainAP;
                        } catch (e) { /* no frameset — L2/L3 still works */ }
                        __heavyT1('hpaL2', __tEntry);
                        return table;
                    }
                } catch (e) {
                    console.warn('[hpa] L2: deserialize failed:', e.message);
                }
            }

            // Full compile (first load or cache miss).
            console.log('[hpa] L3: full compile (L2 miss)');
            { const __t = __heavyT0('hpaCompile'); _hpaTable = hpaCompile(rawText, SECTOR_DATA, terrainAP, wjump, sealed, liveTerrain); __heavyT1('hpaCompile', __t); }
            _hpaTableKey = key;
            try {
                top.__hpaTable = _hpaTable;
                top.__hpaTableKey = key;
                top.__hpaTerrainAP = terrainAP;
            } catch (e) { /* no frameset — L2/L3 still works */ }

            // Defer serialization so UI panels (which call hpaGetTable
            // synchronously via setTimeout(0) in the dispatcher) can start
            // rendering first. The table is already in L1 cache, so the next
            // hpaGetTable() call returns immediately. Serialization +
            // GM_setValue runs in a follow-up macrotask. See ADR 011.
            setTimeout(() => {
                try {
                    const serialized = hpaSerializeTable(_hpaTable, key);
                    console.log('[hpa] L2: persisting ' + (serialized.length / 1024 / 1024).toFixed(1) + ' MB');
                    GM_setValue('logistics_hpa_macro_v1', serialized);
                    console.log('[hpa] L2: persist OK');
                } catch (e) {
                    console.warn('[hpa] L2: persist FAILED:', e.message);
                }
            }, 0);

            __heavyT1('hpaL3', __tEntry);
            return _hpaTable;
        } catch (e) {
            console.error('hpaGetTable: compile failed:', e.message);
            _hpaTable = null;
            _hpaTableKey = null;
            __heavyT1('hpaErr', __tEntry);
            return null;
        }
    }

    // >> Route adapter — converts HPA* route to legacy {legs, totalAP} format.
    // Maps fragment names back to canonical (e.g. "Fragment-A" →
    // "Fragment-0") and adds tileIds to each leg. Returns null when HPA*
    // says unreachable.
    function hpaFindRouteLegacy(table, fromSector, fromXY, toSector, toXY) {
        if (!table) return null;
        const route = hpaFindRoute(table, fromSector, fromXY, toSector, toXY);
        if (!route) return null;
        for (const leg of route.legs) {
            const canonical = _resolveSectorName(leg.sector);
            if (canonical) leg.sector = canonical;
            const sd = getSectorData(leg.sector);
            if (sd) {
                leg.tileIds = leg.path.map(p => sd.start + p.x * sd.rows + p.y);
            } else {
                leg.tileIds = [];
            }
        }
        return route;
    }

    // >> Same-sector all-distances adapter — bridges HPA's Map-returning
    // hpaLocalDijkstraCached to the plain-object shape legacy callers
    // (getSectorAllDistances, simTravelAP via dijCache) expect.
    // Resolves the fragment for (sectorName, x, y) so Fragment-B
    // queries hit the West fragment's grid, not a merged grid.
    // Returns { "x,y": apCost } or null when the table/sector is missing.
    function hpaSectorAllDistances(table, sectorName, x, y) {
        if (!table) return null;
        const frag = hpaResolveFragment(table.sectors, sectorName, x, y);
        const dist = hpaLocalDijkstraCached(table, frag, x, y);
        if (!dist) return null;
        const out = {};
        for (const [k, v] of dist) {
            if (isFinite(v)) out[k] = v;
        }
        return out;
    }

    // --- 15. Rich Nav HUD ---

    // >> Ambush recovery state (module-level, survives across flyToCoords calls)
    // knownAmbushTiles — tile IDs where cloaked/hidden NPCs ambushed us.
    // resumingAfterAmbush — flag so flyToCoords doesn't clear ambush tiles on resume.
    let knownAmbushTiles = new Set();
    let resumingAfterAmbush = false;

    function resumeFlightAfterAmbush() {
        const saved = GM_getValue('logistics_ambush_resume', null);
        if (!saved) return;
        if (Date.now() - saved.timestamp > 5 * 60 * 1000) {
            GM_deleteValue('logistics_ambush_resume');
            return;
        }
        GM_deleteValue('logistics_ambush_resume');
        if (saved.ambushTileId != null) {
            knownAmbushTiles.add(saved.ambushTileId);
        }
        resumingAfterAmbush = true;
        const ov = document.createElement('div');
        ov.style.cssText = 'position:fixed; top:0; left:0; width:100%; background:#003355; color:#fff; text-align:center; padding:6px; z-index:999999; font-weight:bold; font-size:13px; border-bottom:2px solid #0088ff;';
        ov.innerText = '\u2708 Resuming flight to ' + saved.destLabel + ' (avoiding ambush tile)...';
        document.body.appendChild(ov);
        setTimeout(() => ov.remove(), 3000);
        setTimeout(() => {
            flyToCoords(saved.target, saved.destLabel);
        }, 500);
    }

    // >> Monster sidestep helpers
    // The nav screen is a R x C grid (grid cell 0 ... grid cell N).
    // navSizeVer=R rows, navSizeHor=C cols. The player is at the centre —
    // grid center cell (center row, center col).
    // Monsters / NPCs appear with class "navEntity" on the <td>.
    //
    // Tile IDs are computed arithmetically from userloc and sector dimensions,
    // NOT read from the nav grid HTML. The nav grid HTML can have stale or
    // incorrect tile IDs (e.g. after replaceHtml GC churn, or when the center
    // ship tile has no <a> tag). The formula: tileId = sectorStart + x*rows + y
    // so east (dx=+1) = +rows, north (dy=-1) = -1.

    const NAV_MAX_FIELD = N_CELLS;

    // >> Live terrain scraper — decode terrain types from the #navarea HTML.
    // The nav page fully exposes terrain via image filename prefixes:
    //   navOpen cells                 -> terrain in the inner <img> src
    //                                    (.../backgrounds/<prefix><n>.png)
    //   navStructure/navEntity/navStructure   -> terrain in the <td> inline style
    //                                    background-image:url(...) (the inner
    //                                    <img> is the FOREGROUND icon, not terrain)
    //   navBlocked                  -> 'b' (blocked)
    // map_data.txt is user-maintained and proven unreliable: e.g. Sector-X
    // declares 38 terrain rows but SECTOR_DATA says 40, so the 2 missing rows
    // pad with 'b' and make any destination there permanently unreachable (the
    // station at [27,39]). Live terrain is ground truth and always wins over
    // map_data (including padded 'b'). Accumulated into GM_setValue and
    // overlaid in hpaParseMap(). See ADR 009.
    const TERRAIN_PREFIX_MAP = {
        'terrain_a': 'f', 'terrain_b': 'g', 'terrain_c': 'e', 'terrain_d': 'o', 'terrain_e': 'v', 'terrain_f': 'm'
    };

    // >> Read the 9x11 nav grid, decode terrain, return
    // { sector: canonicalName, tiles: { "x,y": char } } or null when not on a
    // nav page / unknown sector. Pure w.r.t. the DOM (no GM_* side effects);
    // scrapeAndStoreTerrain() handles persistence.
    function scrapeNavTerrain() {
        const navarea = document.getElementById('navarea');
        if (!navarea) return null;                      // not on the nav page
        const sectorEl = document.getElementById('sector');
        const sectorName = sectorEl ? sectorEl.textContent.trim() : null;
        if (!sectorName) return null;
        const canonical = _resolveSectorName(sectorName);
        if (!canonical) return null;                    // unknown sector
        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        const uloc = w.userloc;
        if (uloc === undefined || uloc === null) return null;
        const player = getLocalCoordsFromTileId(uloc, canonical);
        if (!player) return null;
        const playerX = player.x, playerY = player.y;
        const sd = getSectorData(canonical);
        if (!sd) return null;
        const navSizeHor = w.navSizeHor || 11;
        const navSizeVer = w.navSizeVer || 9;
        const centerCol = Math.floor(navSizeHor / 2);
        const centerRow = Math.floor(navSizeVer / 2);
        const tiles = {};
        const count = navSizeHor * navSizeVer;
        for (let n = 0; n < count; n++) {
            const td = document.getElementById('navCell' + n);
            if (!td) continue;
            const col = n % navSizeHor;
            const row = Math.floor(n / navSizeHor);
            const absX = playerX + (col - centerCol);
            const absY = playerY + (row - centerRow);
            // Skip tiles outside sector bounds.
            if (absX < 0 || absY < 0 || absX >= sd.cols || absY >= sd.rows) continue;

            let char = null;
            if (td.classList.contains('navBlocked')) {
                char = 'b';
            } else {
                // Terrain image: <td> inline background-image (navStructure/
                // navEntity/navStructure) or inner <img> src (navOpen).
                let url = null;
                const style = td.getAttribute('style') || '';
                const sm = style.match(/background-image:\s*url\(["']?([^"')]+)["']?\)/);
                if (sm) {
                    url = sm[1];
                } else {
                    const img = td.querySelector('img');
                    if (img) url = img.getAttribute('src') || '';
                }
                if (url) {
                    const fname = url.substring(url.lastIndexOf('/') + 1).replace(/\.png$/i, '');
                    const pm = fname.match(/^([a-z_]+?)(\d+|max)$/);
                    if (pm) char = TERRAIN_PREFIX_MAP[pm[1]] || null;
                }
            }
            // Unknown terrain prefixes are skipped (never stored) — hard-fail
            // policy: no guesses for tiles we can't decode.
            if (char !== null) tiles[absX + ',' + absY] = char;
        }
        return { sector: canonical, tiles };
    }

    // >> IIFE-bridge: scrape + merge into the GM terrain store. Sets a dirty
    // flag when a tile is newly discovered or changes value — the version
    // increment (which invalidates the macro-graph cache) is deferred to the
    // dispatcher so active navigation doesn't trigger a per-step recompile.
    // Confirming already-known terrain does not set the dirty flag. See ADR 011.
    // Called synchronously from the dispatcher on //app/main (part 20).
    function scrapeAndStoreTerrain() {
        const result = scrapeNavTerrain();
        if (!result) return;
        const store = GM_getValue('logistics_terrain_v1', {});
        if (!store[result.sector]) store[result.sector] = {};
        let changed = false;
        for (const [key, char] of Object.entries(result.tiles)) {
            if (store[result.sector][key] !== char) {
                store[result.sector][key] = char;
                changed = true;
            }
        }
        if (changed) {
            GM_setValue('logistics_terrain_v1', store);
            GM_setValue('logistics_terrain_dirty', true);
            console.log('[terrain] ' + result.sector + ': stored ' + Object.keys(result.tiles).length + ' tiles (version bump deferred)');
        }
    }

    function scanNavForMonsters() {
        const monsters = new Set();
        for (let i = 0; i <= NAV_MAX_FIELD; i++) {
            const td = document.getElementById('navCell' + i);
            if (td && td.classList.contains('navEntity')) {
                const a = td.querySelector('a');
                if (a) {
                    const m = (a.getAttribute('onclick') || '').match(/\d+/);
                    if (m) monsters.add(parseInt(m[0], 10));
                }
            }
        }
        return monsters;
    }

    function getNavTileIdAt(dx, dy) {
        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        const uloc = w.userloc;
        if (uloc === undefined || uloc === null) return null;
        const baseTileId = parseInt(uloc.toString(), 10);
        if (isNaN(baseTileId)) return null;
        const sectorEl = document.getElementById('sector');
        const sectorName = sectorEl ? sectorEl.textContent.trim() : null;
        if (!sectorName) return null;
        const secInfo = getSectorData(sectorName);
        if (!secInfo) return null;
        return baseTileId + dx * secInfo.rows + dy;
    }

    function isNavTileClear(dx, dy) {
        const tileId = getNavTileIdAt(dx, dy);
        if (tileId === null) return false;
        for (let i = 0; i <= NAV_MAX_FIELD; i++) {
            const td = document.getElementById('navCell' + i);
            if (!td) continue;
            const a = td.querySelector('a');
            if (!a) continue;
            const m = (a.getAttribute('onclick') || '').match(/\d+/);
            if (m && parseInt(m[0], 10) === tileId) {
                return !td.classList.contains('navEntity') && !td.classList.contains('navBlocked');
            }
        }
        return false;
    }

    function flyToCoords(target, destLabel, onArrive) {
        if (!resumingAfterAmbush) {
            knownAmbushTiles.clear();
        }
        resumingAfterAmbush = false;
        GM_deleteValue('logistics_ambush_resume');
        const tx = target.x, ty = target.y;
        const targetSector = target.sector || null;
        const coordsEl = document.getElementById('coords');
        const sectorEl = document.getElementById('sector');
        if (!coordsEl || !sectorEl) {
            alert('Cannot read current sector/coords from the nav screen.');
            return;
        }
        const current = parseCoords(coordsEl.innerText);
        const sectorName = sectorEl.textContent.trim();

        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        const userlocVal = w.userloc;
        if (userlocVal === undefined || userlocVal === null) {
            alert('Could not read "userloc" from the nav page.');
            return;
        }
        const startTileId = parseInt(userlocVal.toString(), 10);
        if (isNaN(startTileId)) {
            alert('Could not parse current tile id from "userloc".');
            return;
        }

        // Build route: single-leg (same sector) or multi-leg (cross-sector via wormholes).
        let legs;
        if (targetSector && targetSector !== sectorName) {
            const route = getCrossSectorRoute(sectorName, startTileId, current.x, current.y, targetSector, tx, ty);
            if (!route || !route.legs || route.legs.length === 0) {
                alert(`No cross-sector path found from ${sectorName} [${current.x},${current.y}] to ${targetSector} [${tx},${ty}].`);
                return;
            }
            legs = route.legs;
        } else {
            const result = logisticsGetSectorPath(sectorName, startTileId, current.x, current.y, tx, ty);
            if (!result || !result.tileIds || result.tileIds.length === 0) {
                alert(`No local path found within sector "${sectorName}" from [${current.x},${current.y}] to [${tx},${ty}].`);
                return;
            }
            legs = [{ sector: sectorName, path: result.path, tileIds: result.tileIds }];
        }

        let cancelled = false;
        const overlay = document.createElement('div');
        overlay.style.cssText = 'position:fixed; top:0; left:0; width:100%; background:#003355; color:#fff; text-align:center; padding:6px; z-index:999999; font-weight:bold; font-size:13px; border-bottom:2px solid #0088ff; display:flex; align-items:center; justify-content:center; gap:12px;';
        document.body.appendChild(overlay);
        const cancelBtn = document.createElement('button');
        cancelBtn.textContent = 'Cancel';
        cancelBtn.style.cssText = 'background:#882222; color:#fff; border:1px solid #ff4444; border-radius:3px; padding:2px 12px; font-weight:bold; font-size:12px; cursor:pointer; white-space:nowrap;';
        cancelBtn.onclick = function() {
            cancelled = true;
            GM_deleteValue('logistics_ambush_resume');
            setOverlay('\u2708 Flight cancelled.');
            setTimeout(() => overlay.remove(), 2000);
            if (onArrive) onArrive(false);
        };
        overlay.appendChild(cancelBtn);

        function resolveNavFn() {
            if (typeof w.navAjax === 'function') return w.navAjax;
            if (typeof w.nav === 'function') return w.nav;
            return null;
        }

        function currentTileId() {
            const v = w.userloc;
            return (v === undefined || v === null) ? -1 : parseInt(v.toString(), 10);
        }

        function getCurrentSector() {
            const el = document.getElementById('sector');
            return el ? el.textContent.trim() : null;
        }

        function setOverlay(text) {
            const span = overlay.querySelector('.fly-text') || (() => {
                const s = document.createElement('span');
                s.className = 'fly-text';
                s.style.flex = '1';
                overlay.insertBefore(s, overlay.firstChild);
                return s;
            })();
            span.textContent = text;
        }

        function fail(msg) {
            setOverlay(msg);
            setTimeout(() => overlay.remove(), 4000);
            if (onArrive) onArrive(false);
        }

        let legIdx = 0;

        function flyNext() {
            if (cancelled) return;
            const curId = currentTileId();
            const curSector = getCurrentSector();

            // Detect wormhole jump: if the current sector differs from the
            // current leg's sector, find the leg matching the new sector.
            if (curSector !== legs[legIdx].sector) {
                let found = false;
                for (let li = legIdx + 1; li < legs.length; li++) {
                    if (legs[li].sector === curSector) {
                        legIdx = li;
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    fail(`\u26a0 Unexpected sector "${curSector}" after wormhole jump (expected "${legs[legIdx + 1] ? legs[legIdx + 1].sector : '?'}"). Stopping.`);
                    return;
                }
                setOverlay(`\u2708 Wormhole jump complete \u2014 now in ${curSector}. Continuing...`);
            }

            const leg = legs[legIdx];
            const tileIds = leg.tileIds;
            const pathCoords = leg.path;

            let idx = tileIds.indexOf(curId);
            if (idx < 0) {
                // After a wormhole jump, the pre-computed tile IDs for this
                // leg may not match the actual post-jump tile (static map
                // wormhole coordinates can differ from the live game).
                // Recompute the path from the real tile to this leg's endpoint.
                const newCoords = getLocalCoordsFromTileId(curId, curSector);
                if (newCoords) {
                    const legEnd = pathCoords[pathCoords.length - 1];
                    const newResult = logisticsGetSectorPath(curSector, curId, newCoords.x, newCoords.y, legEnd.x, legEnd.y);
                    if (newResult && newResult.tileIds.length > 0) {
                        legs[legIdx] = { sector: curSector, path: newResult.path, tileIds: newResult.tileIds };
                        idx = 0;
                    }
                }
                if (idx < 0) {
                    fail(`\u26a0 Off local path (tile ${curId}, expected one of ${tileIds.length} tiles in ${leg.sector}). Stopping — fly manually.`);
                    return;
                }
            }
            if (idx === tileIds.length - 1) {
                // At the end of this leg.
                if (legIdx === legs.length - 1) {
                    // Final destination.
                    setOverlay(`\u2708 Arrived at ${destLabel}.`);
                    setTimeout(() => overlay.remove(), 2500);
                    if (onArrive) onArrive(true);
                    return;
                }
                // At a wormhole tile — trigger the jump by clicking the
                // "jump to *" link that the game renders on the nav screen.
                const jumpLink = document.querySelector('a[href*="warpAjax"]');
                if (!jumpLink) {
                    fail('\u26a0 No wormhole jump link found on page. Stopping.');
                    return;
                }
                const beforeSector = curSector;
                setOverlay(`\u2708 Triggering wormhole jump (leg ${legIdx + 1}/${legs.length})...`);
                jumpLink.click();

                const deadline = Date.now() + 8000;
                (function waitForJump() {
                    if (cancelled) return;
                    const newSector = getCurrentSector();
                    if (newSector !== beforeSector) {
                        setTimeout(flyNext, 100);
                        return;
                    }
                    if (Date.now() > deadline) {
                        fail('\u26a0 Wormhole jump did not trigger. Try moving manually and re-clicking.');
                        return;
                    }
                    setTimeout(waitForJump, 50);
                })();
                return;
            }

            const curCoord = pathCoords[idx];
            const dirX = pathCoords[idx + 1].x - curCoord.x;
            const dirY = pathCoords[idx + 1].y - curCoord.y;
            let targetIdx = idx + 1;
            for (let j = idx + 2; j < tileIds.length; j++) {
                const stepX = pathCoords[j].x - pathCoords[j - 1].x;
                const stepY = pathCoords[j].y - pathCoords[j - 1].y;
                if (stepX !== dirX || stepY !== dirY) break;
                if (Math.abs(pathCoords[j].x - curCoord.x) > 5) break;
                if (Math.abs(pathCoords[j].y - curCoord.y) > 4) break;
                targetIdx = j;
            }
            const targetId = tileIds[targetIdx];
            const navFn = resolveNavFn();
            if (!navFn) {
                fail('\u26a0 nav function (navAjax/nav) not found on page. Stopping.');
                return;
            }

            // >> Monster guard — scan nav screen and sidestep if blocked
            const monsterSet = scanNavForMonsters();
            for (const at of knownAmbushTiles) { monsterSet.add(at); }
            if (monsterSet.size > 0) {
                for (let j = idx + 1; j <= targetIdx; j++) {
                    if (monsterSet.has(tileIds[j])) {
                        targetIdx = j - 1;
                        break;
                    }
                }
            }

            if (targetIdx === idx) {
                // Monster is on the very next tile — sidestep around it.
                if (idx + 1 >= tileIds.length) {
                    fail('\u26a0 Monster at destination. Stopping \u2014 fly manually.');
                    return;
                }

                const perpOptions = [[-dirY, dirX], [dirY, -dirX]];
                let sidestepped = false;

                const moveAndWait = (tileId, afterMs, onSuccess, onFailMsg) => {
                    GM_setValue('logistics_ambush_resume', {
                        target: { x: tx, y: ty, sector: targetSector },
                        destLabel: destLabel,
                        ambushTileId: tileId,
                        timestamp: Date.now()
                    });
                    const before = currentTileId();
                    try { navFn(tileId); } catch (e) { GM_deleteValue('logistics_ambush_resume'); fail('\u26a0 nav() threw during sidestep: ' + e.message); return; }
                    const dl = Date.now() + 6000;
                    (function wait() {
                        if (cancelled) { GM_deleteValue('logistics_ambush_resume'); return; }
                        if (currentTileId() !== before) { GM_deleteValue('logistics_ambush_resume'); setTimeout(onSuccess, afterMs); return; }
                        if (Date.now() > dl) { GM_deleteValue('logistics_ambush_resume'); fail(onFailMsg); return; }
                        setTimeout(wait, 50);
                    })();
                };

                for (const [pDx, pDy] of perpOptions) {
                    if (!isNavTileClear(pDx, pDy)) continue;
                    const sidestepId = getNavTileIdAt(pDx, pDy);
                    if (!sidestepId) continue;
                    sidestepped = true;
                    const dirName = pDx > 0 ? 'east' : pDx < 0 ? 'west' : pDy > 0 ? 'south' : 'north';
                    setOverlay('\u26a0 Monster in path \u2014 sidestepping ' + dirName + '...');

                    moveAndWait(sidestepId, 150, () => {
                        // After sidestepping, loop: move forward until the
                        // rejoin tile (back to original path) is clear, then
                        // rejoin.  This handles any number of consecutive
                        // monsters on the original path.
                        let forwardCount = 0;
                        const MAX_FORWARD = 5;

                        const moveForwardOrRejoin = () => {
                            // Can we rejoin the original path?  Only attempt
                            // after at least 1 forward move (otherwise we'd
                            // rejoin onto the starting tile, going nowhere).
                            const rejoinClear = forwardCount > 0 && isNavTileClear(-pDx, -pDy);
                            const rejoinId = forwardCount > 0 ? getNavTileIdAt(-pDx, -pDy) : null;
                            if (rejoinClear) {
                                const backId = rejoinId;
                                if (!backId) { fail('\u26a0 Cannot find path-rejoin tile. Stopping.'); return; }
                                setOverlay('\u26a0 Rejoining original path...');
                                moveAndWait(backId, 150, () => {
                                    setOverlay('\u2708 Monster avoided \u2014 resuming flight to ' + destLabel + '...');
                                    flyNext();
                                }, '\u26a0 Rejoin move did not complete. Stopping.');
                                return;
                            }
                            // Can't rejoin yet — move forward on the offset path.
                            if (forwardCount >= MAX_FORWARD) {
                                fail('\u26a0 Too many consecutive monsters (' + MAX_FORWARD + '+). Stopping \u2014 fly manually.');
                                return;
                            }
                            if (!isNavTileClear(dirX, dirY)) {
                                fail('\u26a0 Monster on sidestep forward path. Stopping.');
                                return;
                            }
                            const fwdId = getNavTileIdAt(dirX, dirY);
                            if (!fwdId) { fail('\u26a0 Cannot find forward tile after sidestep. Stopping.'); return; }
                            forwardCount++;
                            setOverlay('\u26a0 Moving forward past monster' + (forwardCount > 1 ? 's' : '') + '...');
                            moveAndWait(fwdId, 150, moveForwardOrRejoin, '\u26a0 Forward move did not complete. Stopping.');
                        };

                        moveForwardOrRejoin();
                    }, '\u26a0 Sidestep move did not complete. Stopping.');
                    break;
                }

                if (!sidestepped) {
                    fail('\u26a0 Monster directly ahead and no sidestep tile available. Stopping \u2014 fly manually.');
                }
                return;
            }

            const legInfo = legs.length > 1 ? ` (leg ${legIdx + 1}/${legs.length}, ${leg.sector})` : '';
            setOverlay(`\u2708 Flying to ${destLabel}${legInfo} (${tileIds.length - idx - 1} tiles left, jumping ${targetIdx - idx})...`);
            const beforeId = curId;
            GM_setValue('logistics_ambush_resume', {
                target: { x: tx, y: ty, sector: targetSector },
                destLabel: destLabel,
                ambushTileId: targetId,
                timestamp: Date.now()
            });
            try {
                __perfMark('flight_tile_start');
                navFn(targetId);
            } catch (e) {
                GM_deleteValue('logistics_ambush_resume');
                fail(`\u26a0 nav() threw: ${e.message}. Stopping.`);
                return;
            }

            const deadline = Date.now() + 6000;
            (function waitForMove() {
                if (cancelled) { GM_deleteValue('logistics_ambush_resume'); return; }
                if (currentTileId() !== beforeId) {
                    GM_deleteValue('logistics_ambush_resume');
                    __perfMark('flight_tile_end');
                    setTimeout(flyNext, 80);
                    return;
                }
                if (Date.now() > deadline) {
                    GM_deleteValue('logistics_ambush_resume');
                    fail(`\u26a0 Nav did not update after moving to tile ${targetId}. Stopping.`);
                    return;
                }
                setTimeout(waitForMove, 50);
            })();
        }

        flyNext();
    }

    function flyHereToStep(onArrive) {
        const activeData = GM_getValue('logistics_route_v5', { steps: [] });
        const steps = activeData.steps || [];
        if (steps.length === 0) {
            alert('No active route step to fly to.');
            return;
        }
        const target = parseCoords(steps[0].location);
        flyToCoords(target, steps[0].location, onArrive);
    }

    // --- 16. Reality Clamp ---
    //     Reads the ACTUAL stock / free space for a commodity row straight off
    //     the trade DOM. This is the last line of defense against bookkeeper
    //     tick-projection drift caused by other players trading between the
    //     moment bookkeeper logged the building and now.
    function getTradeRowLimits(commodityId, action, commodityName) {
        let stock = NaN, cap = NaN, freeSpace = NaN, shipStock = NaN;

        if (isTradingOutpostPage()) {
            // Transit Hub: structure free space is a single global figure
            // printed at the top of the trade screen.
            let m = document.body.innerText.match(/Free space in building:?\s*([\d,]+)/i);
            if (m) freeSpace = parseInt(m[1].replace(/,/g, ''), 10);

            // For dropoffs (sell), the limiting factor is how much of the
            // commodity is still ON the ship. The TH Ship table keeps the
            // row even after stock hits 0 (the useMax link text becomes 0),
            // so we must read the ship-side amount to detect a completed
            // dropoff — otherwise the script would re-fill the input every
            // reload and never advance past this step.
            if (action === 'sell') {
                let shipInput = findTradeInputForCommodity('sell', commodityName || commodityId);
                if (shipInput) {
                    let row = shipInput.closest('tr');
                    if (row) {
                        let useMaxLink = row.querySelector('a[href*="useMax"]');
                        if (useMaxLink) {
                            let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                            if (s !== '') shipStock = parseInt(s, 10);
                        }
                        if (isNaN(shipStock)) {
                            let cells = Array.from(row.querySelectorAll('td'));
                            if (cells.length > 2) {
                                let s = cells[2].textContent.replace(/[^\d]/g, '');
                                if (s !== '') shipStock = parseInt(s, 10);
                            }
                        }
                    }
                }
                // If the ship row is gone entirely, the commodity was fully
                // dropped — treat shipStock as 0 so the caller skips the fill.
                if (isNaN(shipStock)) shipStock = 0;
            }

            // For pickups (buy), read structure stock from the comm row.
            if (action !== 'sell') {
                let imgs = document.querySelectorAll('img[src*="/' + commodityId + '"]');
                for (let img of imgs) {
                    const row = img.closest('tr');
                    if (!row) continue;
                    const input = row.querySelector(tradeInputSelectorFor('buy'));
                    if (!input) continue;

                    if (commodityName) {
                        const rowName = readRowCommodityName(row);
                        if (rowName.toLowerCase() !== commodityName.toLowerCase()) continue;
                    }

                    const useMaxLink = row.querySelector('a[href*="useMax"]');
                    if (useMaxLink) {
                        let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                        if (s) stock = parseInt(s, 10);
                    }
                    if (isNaN(stock)) {
                        const cells = Array.from(row.querySelectorAll('td'));
                        if (cells.length > 2) {
                            let s = cells[2].textContent.replace(/[^\d]/g, '');
                            if (s) stock = parseInt(s, 10);
                        }
                    }
                    break;
                }
            }

            return {
                found: !isNaN(stock) || !isNaN(freeSpace) || !isNaN(shipStock),
                stock: stock,
                cap: cap,
                freeSpace: freeSpace,
                shipStock: shipStock
            };
        }

        // Standard trade screens (trade_a / trade_b / trade_c).
        // Building free space: read from the structure table footer.
        let baseRowEl = document.querySelector('tr[id^="baserow"]');
        if (baseRowEl) {
            let baseTable = baseRowEl.closest('table');
            if (baseTable) {
                let m = baseTable.innerText.match(/free\s*space:?\s*([\d,]+)/i);
                if (m) freeSpace = parseInt(m[1].replace(/,/g, ''), 10);
            }
        }

        // Stock: read from the structure (buy) row. In the trade table
        // the columns are: [0]icon [1]name [2]Amount(stock) [3]Balance
        // [4]Min [5]Max [6]Price [7]input. The stock cell (cells[2]) contains
        // a <a href="javascript:useMax('buy',N)"> link whose text is the
        // authoritative stock count.
        const imgs = document.querySelectorAll('img[src*="/' + commodityId + '"]');
        for (let img of imgs) {
            const row = img.closest('tr');
            if (!row) continue;
            const input = row.querySelector(tradeInputSelectorFor('buy'));
            if (!input) continue;

            if (commodityName) {
                const rowName = readRowCommodityName(row);
                if (rowName.toLowerCase() !== commodityName.toLowerCase()) continue;
            }

            const cells = Array.from(row.querySelectorAll('td'));

            // Primary: the useMax link holds the real stock count.
            const useMaxLink = row.querySelector('a[href*="useMax"]');
            if (useMaxLink) {
                let s = useMaxLink.textContent.replace(/[^\d]/g, '');
                if (s) stock = parseInt(s, 10);
            }

            // Fallback: cells[2] is the "Amount" column in trade tables.
            if (isNaN(stock) && cells.length > 2) {
                let s = cells[2].textContent.replace(/[^\d]/g, '');
                if (s) stock = parseInt(s, 10);
            }

            // Generic fallback: first numeric non-input cell after the name.
            if (isNaN(stock)) {
                for (let i = 2; i < cells.length; i++) {
                    if (cells[i].querySelector('input')) continue;
                    let t = cells[i].textContent.replace(/[^\d]/g, '').trim();
                    if (t) {
                        let n = parseInt(t, 10);
                        if (!isNaN(n) && n >= 0) { stock = n; break; }
                    }
                }
            }

            // Cap: cells[5] is the "Max" column (per-commodity stock cap).
            if (cells.length > 5) {
                let s = cells[5].textContent.replace(/[^\d]/g, '');
                if (s) cap = parseInt(s, 10);
            }
            break;
        }

        if (action === 'sell' && !isNaN(stock) && !isNaN(cap) && cap > 0) {
            freeSpace = Math.max(0, cap - stock);
        }

        return {
            found: !isNaN(stock) || !isNaN(freeSpace),
            stock: stock,
            cap: cap,
            freeSpace: freeSpace
        };
    }

    function processTradeDOMBeforeUnload() {
        if (window.hasProcessedTrade) return;
        window.hasProcessedTrade = true;

        let actualTraded = { dropoffs: {}, pickups: {} };

        let inputs = document.querySelectorAll(allTradeInputSelector());
        inputs.forEach(input => {
            let val = parseInt(input.value, 10);
            if (val > 0) {
                let row = input.closest('tr');
                if (row) {
                    let name = readRowCommodityName(row);
                    if (name) {
                        let kind = classifyTradeInput(input);
                        if (kind === 'sell') {
                            actualTraded.dropoffs[name] = val;
                        } else if (kind === 'buy') {
                            actualTraded.pickups[name] = val;
                        }
                    }
                }
            }
        });

        if (Object.keys(actualTraded.dropoffs).length === 0 && Object.keys(actualTraded.pickups).length === 0) {
            window.hasProcessedTrade = false;
            return;
        }

        // Only update live cargo optimistically. Do NOT shift the route step,
        // mutate bookkeeper data, or flag for recalc here — the trade hasn't
        // been confirmed by the server yet. syncNodeWithReality (which runs on
        // the reloaded trade screen) reads the actual post-trade stock and
        // triggers a recalc if the bookkeeper data drifted. This prevents the
        // route from advancing past a location whose trade was rejected.
        let liveStr = GM_getValue('logistics_live_cargo', '');
        let liveCargo = parseLiveCargo(liveStr);

        Object.entries(actualTraded.dropoffs).forEach(([name, amt]) => {
            let key = name.toLowerCase();
            liveCargo[key] = (liveCargo[key] || 0) - amt;
            if (liveCargo[key] <= 0) delete liveCargo[key];
        });

        Object.entries(actualTraded.pickups).forEach(([name, amt]) => {
            let key = name.toLowerCase();
            liveCargo[key] = (liveCargo[key] || 0) + amt;
        });

        GM_setValue('logistics_live_cargo', stringifyLiveCargo(liveCargo));
    }

    function injectTradeHUD() {
        // Detect ship capacity and aux_hold from trade screen JS variables
        const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        if (typeof w.ship_space !== 'undefined' && w.ship_space > 0) {
            GM_setValue('logistics_ship_space', w.ship_space);
        }
        if (typeof w.mag_scoop === 'undefined' || !w.mag_scoop) {
            GM_setValue('logistics_mag_scoop_used', 0);
        }

        let sectorState = GM_getValue('raw_bookkeeper_data', []);
        let currentCoords = "";
        try { currentCoords = document.getElementById('coords').innerText; } catch(e){}
        if (!currentCoords) currentCoords = GM_getValue('logistics_trade_loc', '');

        let nodeIndex = sectorState.findIndex(n => normalizeCoords(n.location) === normalizeCoords(currentCoords));
        if (nodeIndex !== -1) {
            let syncTriggered = syncNodeWithReality(sectorState[nodeIndex]);
            if (syncTriggered) {
                GM_setValue('raw_bookkeeper_data', sectorState);
                // Hard-fail policy: recalc throws without userloc/map data.
                // Don't let that abort the rest of the trade HUD injection —
                // flag a retry for the next page load instead.
                try { recalculateRouteOnTheFly(sectorState); }
                catch (e) {
                    GM_setValue('logistics_needs_recalc', true);
                    console.error('[logistics-sim] route recalc failed (deferred to next page):', e);
                }
            }
        } else {
            // This location is not in bookkeeper data (hub, TH, or a
            // building that wasn't synced).  processTradeDOMBeforeUnload
            // already updated liveCargo optimistically when the user
            // submitted the trade.  If the reloaded screen shows the
            // trade is fully satisfied, rebuild the route so the step
            // advances.  Completion is detected from liveCargo (which
            // processTradeDOMBeforeUnload updated), NOT from building
            // stock — structure stock > 0 doesn't mean incomplete.
            const hubData = GM_getValue('logistics_route_v5', { steps: [], history: [] });
            const hubStep = (hubData.steps || [])[0];
            if (hubStep && normalizeCoords(hubStep.location) === normalizeCoords(currentCoords)) {
                let liveCargo = parseLiveCargo(GM_getValue('logistics_live_cargo', ''));
                let hubComplete = true;
                Object.entries(hubStep.dropoffs || {}).forEach(([name, data]) => {
                    // Dropoff is complete when liveCargo no longer holds
                    // the planned amount (processTradeDOMBeforeUnload
                    // subtracted it on submit).
                    let have = liveCargo[(name || '').toLowerCase()] || 0;
                    if (have >= data.amount) hubComplete = false;
                });
                Object.entries(hubStep.pickups || {}).forEach(([name, data]) => {
                    // Pickup is complete when liveCargo already holds the
                    // planned amount (processTradeDOMBeforeUnload added it
                    // on submit).
                    let have = liveCargo[(name || '').toLowerCase()] || 0;
                    if (have < data.amount) hubComplete = false;
                });
                if (hubComplete && (Object.keys(hubStep.dropoffs || {}).length > 0 || Object.keys(hubStep.pickups || {}).length > 0)) {
                    try { recalculateRouteOnTheFly(sectorState); }
                    catch (e) {
                        GM_setValue('logistics_needs_recalc', true);
                        console.error('[logistics-sim] route recalc failed (deferred to next page):', e);
                    }
                }
            }
        }

        const interceptor = document.createElement('script');
        interceptor.textContent = `
            (function() {
                if (window.__logisticsIntercept) return;
                window.__logisticsIntercept = true;

                const origSubmit = HTMLFormElement.prototype.submit;

                document.addEventListener('click', function(e) {
                    if (e.target.tagName === 'INPUT' && (e.target.type === 'submit' || e.target.type === 'image')) {
                        let form = e.target.closest('form');
                        if (form && e.target.name) {
                            let hidden = document.createElement('input');
                            hidden.type = 'hidden';
                            hidden.name = e.target.name;
                            hidden.value = e.target.value || '1';
                            form.appendChild(hidden);
                        }
                    }
                }, true);

                HTMLFormElement.prototype.submit = function() {
                    window.dispatchEvent(new CustomEvent('logisticsTradeSubmitted'));
                    let form = this;
                    setTimeout(() => { origSubmit.call(form); }, 10);
                };

                document.addEventListener('submit', function(e) {
                    e.preventDefault();
                    window.dispatchEvent(new CustomEvent('logisticsTradeSubmitted'));
                    let form = e.target;
                    setTimeout(() => { origSubmit.call(form); }, 10);
                }, true);
            })();
        `;
        document.documentElement.appendChild(interceptor);
        interceptor.remove();

        window.addEventListener('logisticsTradeSubmitted', () => {
            let inputs = document.querySelectorAll(allTradeInputSelector());
            if (inputs.length > 0) {
                const overlay = document.createElement('div');
                overlay.style.cssText = 'position:fixed; top:0; left:0; width:100%; background:#004400; color:#fff; text-align:center; padding:8px; z-index:999999; font-weight:bold; font-size:14px; border-bottom:2px solid #0f0; box-shadow:0px 4px 10px rgba(0,0,0,0.8);';
                overlay.innerText = 'Logistics Sync: Predicting Cargo state... Auto-Adapting Route...';
                document.body.appendChild(overlay);
            }
            processTradeDOMBeforeUnload();
        });

        const activeData = GM_getValue('logistics_route_v5', { steps: [], history: [] });
        const safeSteps = activeData.steps || [];
        if (safeSteps.length === 0) return;

        const currentStep = safeSteps[0];

        if (GM_getValue('logistics_auto_step', false) && checkStuckStop(currentStep.location)) {
            return;
        }

        if (normalizeCoords(currentStep.location) !== normalizeCoords(currentCoords)) {
            const staleHud = document.createElement('div');
            staleHud.style.cssText = `background: #442200; color: #fff; text-align: center; padding: 10px; border-bottom: 2px solid #ffaa00; font-family: Verdana, sans-serif; font-size: 13px;`;
            staleHud.innerHTML = `
                <div style="margin-bottom: 6px; font-size: 14px;"><strong>Trade complete \u2014 next stop is elsewhere</strong></div>
                <div style="font-size: 11px; color: #ffaa88; margin-bottom: 10px;">You're on the trade screen at ${currentCoords}, but the route's next step is at ${currentStep.location} ${currentStep.name}. Close this screen to continue.</div>
                <div style="border: 1px solid #00ff00; background: #001100; padding: 6px;">
                    <div id="qol-status" style="color: #00ff00; font-weight: bold; font-size: 12px; margin-bottom: 4px; min-height: 14px;">${qolDescribeNextStep()}</div>
                    <button id="qol-next-btn" style="width: 100%; cursor: pointer; padding: 6px; background: #004400; color: #fff; border: 1px solid #0f0; font-weight: bold; font-size: 12px;">\u25b6 Next Step</button>
                    <div style="display: flex; gap: 4px; margin-top: 4px;">
                        <button id="qol-auto-btn" style="flex: 1; cursor: pointer; padding: 4px; background: #003a00; color: #88ff88; border: 1px solid #0f0; font-weight: bold; font-size: 11px;">\u23a9 Auto Run</button>
                        <button id="qol-stop-btn" disabled style="flex: 1; cursor: pointer; padding: 4px; background: #3a0000; color: #ff8888; border: 1px solid #f00; font-weight: bold; font-size: 11px; opacity: 0.5;">\u23cf Stop</button>
                    </div>
                </div>
            `;
            document.body.insertBefore(staleHud, document.body.firstChild);
            document.getElementById('qol-next-btn').addEventListener('click', () => {
                const statusEl = document.getElementById('qol-status');
                if (statusEl) statusEl.innerText = qolDescribeNextStep();
                qolNextStep();
                if (statusEl) statusEl.innerText = qolDescribeNextStep();
            });
            bindQolAutoButtons();
            bindQolHotkey();
            if (GM_getValue('logistics_auto_step', false)) {
                __perfMark('qol_next');
                __perfMark('nav_return_click');
                GM_deleteValue('logistics_trade_loc');
                try { top.frames.main.location.href = '//app/main?nav=1'; }
                catch (err) { top.location.href = '//app/main?nav=1'; }
                return;
            }
            autoStepResume();
            return;
        }

        let baseFreeSpace = getTrueBaseFreeSpace();
        let safeSpaceForPickups = baseFreeSpace !== null ? baseFreeSpace : 999999;

        let dropoffsHtml = '';
        let hasDrops = Object.keys(currentStep.dropoffs || {}).length > 0;
        let realityWarnings = [];
        let realityPatched = false;

        Object.entries(currentStep.dropoffs || {}).forEach(([name, data]) => {
            let limits = getTradeRowLimits(data.id, 'sell', name);
            let planned = data.amount;
            let realCap = (limits.found && !isNaN(limits.freeSpace)) ? limits.freeSpace : planned;
            let realShip = (limits.found && !isNaN(limits.shipStock)) ? limits.shipStock : planned;
            let dropAmt = Math.min(planned, realCap, realShip);
            dropAmt = Math.max(0, dropAmt);

            let clamped = limits.found && !isNaN(limits.freeSpace) && realCap < planned;
            let clampedByShip = limits.found && !isNaN(limits.shipStock) && realShip < planned;
            let clampNotes = [];
            if (clamped) clampNotes.push(`structure free space ${limits.freeSpace}`);
            if (clampedByShip) clampNotes.push(`ship stock ${limits.shipStock}`);
            dropoffsHtml += `<div style="margin-bottom: 4px;">Drop off <strong>${dropAmt} ${name}</strong>${clampNotes.length ? ` <span style="color:#ffaa00; font-size:10px;"><br>⚠ Reality-clamped from ${planned} — ${clampNotes.join(' + ')}</span>` : ''}</div>`;

            if (dropAmt > 0) autoFillTrade('sell', name, dropAmt);
            safeSpaceForPickups += dropAmt;

            if (clamped || clampedByShip) {
                // Hub steps (nodeIndex === -1, e.g. player-owned Trading
                // Hub) are not in the bookkeeper data, so "other players
                // traded" drift detection does not apply — ship stock < plan
                // just means a partial delivery or stale liveCargo.
                if (nodeIndex !== -1) {
                    realityWarnings.push(`${name} dropoff ${planned} → ${dropAmt} (${clampNotes.join(' + ')})`);
                    if (sectorState[nodeIndex].dropoffs) {
                        let nk = Object.keys(sectorState[nodeIndex].dropoffs).find(k => k.toLowerCase() === name.toLowerCase());
                        if (nk) {
                            sectorState[nodeIndex].dropoffs[nk].amount = dropAmt;
                            realityPatched = true;
                        }
                    }
                } else {
                    GM_setValue('logistics_needs_recalc', true);
                }
                data.amount = dropAmt;
            }
        });

        let pickupsHtml = '';
        let hasPicks = Object.keys(currentStep.pickups || {}).length > 0;
        Object.entries(currentStep.pickups || {}).forEach(([name, data]) => {
            let limits = getTradeRowLimits(data.id, 'buy', name);
            let planned = data.amount;
            let realStock = (limits.found && !isNaN(limits.stock) && limits.stock >= 0) ? limits.stock : planned;
            let cargoCap = safeSpaceForPickups;
            let safeAmt = Math.min(planned, realStock, cargoCap);
            safeAmt = Math.max(0, safeAmt);

            let clampedByStock = limits.found && !isNaN(limits.stock) && realStock < planned;
            let clampedByCargo = safeAmt < realStock;

            if (safeAmt > 0) {
                let notes = [];
                if (clampedByStock) notes.push(`structure stock ${limits.stock}`);
                if (clampedByCargo) notes.push('cargo cap');
                pickupsHtml += `<div style="margin-bottom: 4px;">Pick up <strong>${safeAmt} ${name}</strong>${notes.length ? ` <span style="color:#ffaa00; font-size:10px;"><br>⚠ Reduced from ${planned} — ${notes.join(' + ')}</span>` : ''}</div>`;
                autoFillTrade('buy', name, safeAmt);
                safeSpaceForPickups -= safeAmt;
            } else {
                pickupsHtml += `<div style="margin-bottom: 4px; color: #ff5555;">Pick up <strong>0 ${name}</strong> <span style="font-size:10px;"><br>(No stock / Cargo Full - 10x AP Penalty Prevented)</span></div>`;
            }

            // NOTE: clampedByCargo (cargo-cap clamp) intentionally does NOT
            // trigger realityPatched / logistics_needs_recalc here.  A mid-route
            // recalc triggered by cargo cap could destabilize cycle blocks —
            // see 19-19-true-ap-density-simulation-engine.js ("cycle
            // block is immutable").  If a partial pickup due to cargo cap
            // causes downstream steps to misfire (e.g. factory doesn't get
            // enough of a commodity), that is the place to revisit.  With the
            // sim (v6.34) and runtime (v6.35) aux_hold fixes, cargo-cap
            // clamping should only occur if another player trades at the
            // building between sim run and arrival — a rare edge case.
            if (clampedByStock) {
                if (nodeIndex !== -1) {
                    realityWarnings.push(`${name} pickup ${planned} → ${safeAmt} (stock ${limits.stock})`);
                    if (sectorState[nodeIndex].pickups) {
                        let nk = Object.keys(sectorState[nodeIndex].pickups).find(k => k.toLowerCase() === name.toLowerCase());
                        if (nk) {
                            sectorState[nodeIndex].pickups[nk].amount = limits.stock;
                            realityPatched = true;
                        }
                    }
                } else {
                    GM_setValue('logistics_needs_recalc', true);
                }
                data.amount = safeAmt;
            }
        });

        // If reality differed from bookkeeper's projection, persist the corrected
        // node state and flag the route for an AP-efficient rework on next load.
        if (realityPatched) {
            GM_setValue('raw_bookkeeper_data', sectorState);
            GM_setValue('logistics_needs_recalc', true);
        }

        let realityWarningHtml = realityWarnings.length > 0
            ? `<div style="background: #664400; color: #ffee88; font-weight: bold; padding: 8px; margin-bottom: 12px; border: 2px solid #ffaa00; text-transform: uppercase;">⚠ Reality mismatch vs bookkeeper projection (other players traded). Amounts clamped to live building state; supply chain reworked for max AP efficiency:<br><span style="font-weight:normal; text-transform:none;">${realityWarnings.join('<br>')}</span></div>`
            : '';

        // Detect error message for space deadlock
        let hasSpaceError = document.body.innerText.toLowerCase().includes('not enough room') || document.body.innerText.toLowerCase().includes('cannot hold');
        let errorWarningHtml = hasSpaceError ? `<div style="background: #cc0000; color: #ffff00; font-weight: bold; padding: 8px; margin-bottom: 12px; border: 2px solid #ffcc00; text-transform: uppercase;">⚠️ Trade Rejected by Server: Use the "Execute ONLY" buttons below to split the transfer into two parts!</div>` : '';

        const hud = document.createElement('div');
        hud.style.cssText = `background: #002200; color: #fff; text-align: center; padding: 10px; border-bottom: 2px solid #0f0; font-family: Verdana, sans-serif; font-size: 13px;`;

        hud.innerHTML = `
            <div style="border: 1px solid #00ff00; background: #001100; padding: 6px; margin-bottom: 10px;">
                <div id="qol-status" style="color: #00ff00; font-weight: bold; font-size: 12px; margin-bottom: 4px; min-height: 14px;">${qolDescribeNextStep()}</div>
                <button id="qol-next-btn" style="width: 100%; cursor: pointer; padding: 6px; background: #004400; color: #fff; border: 1px solid #0f0; font-weight: bold; font-size: 12px;">\u25b6 Next Step</button>
                <div style="display: flex; gap: 4px; margin-top: 4px;">
                    <button id="qol-auto-btn" style="flex: 1; cursor: pointer; padding: 4px; background: #003a00; color: #88ff88; border: 1px solid #0f0; font-weight: bold; font-size: 11px;">\u23a9 Auto Run</button>
                    <button id="qol-stop-btn" disabled style="flex: 1; cursor: pointer; padding: 4px; background: #3a0000; color: #ff8888; border: 1px solid #f00; font-weight: bold; font-size: 11px; opacity: 0.5;">\u23cf Stop</button>
                </div>
            </div>
            <div style="margin-bottom: 10px; font-size: 15px;"><strong>Expected Transfer at ${currentStep.location} ${currentStep.name}</strong></div>
            ${realityWarningHtml}
            ${errorWarningHtml}
            <div style="font-size: 11px; color: #aaa; margin-bottom: 10px;">The script hard-caps Pickups to match your Base Cargo. If a building rejects a dual-trade, split it using the buttons below.</div>

            <div style="display: flex; justify-content: center; gap: 30px; margin-bottom: 15px;">
                <div style="text-align: left; color: #ff8888; background: #220000; padding: 10px; border: 1px solid #ff0000; min-width: 250px; display: flex; flex-direction: column;">
                    <div style="border-bottom: 1px solid #ff4444; margin-bottom: 8px; padding-bottom: 3px;"><strong>STEP 1: TRANSFER TH BUILDING</strong></div>
                    <div style="flex-grow: 1;">${dropoffsHtml || '<em>No dropoffs needed here.</em>'}</div>
                    ${hasDrops && hasPicks ? `<button id="btn-only-drop" style="margin-top: 10px; width: 100%; cursor: pointer; padding: 5px; background: #660000; color: #fff; border: 1px solid #ff4444; font-weight: bold;">📤 Execute ONLY Dropoffs</button>` : ''}
                </div>
                <div style="text-align: left; color: #88ff88; background: #002200; padding: 10px; border: 1px solid #00ff00; min-width: 250px; display: flex; flex-direction: column;">
                    <div style="border-bottom: 1px solid #44ff44; margin-bottom: 8px; padding-bottom: 3px;"><strong>STEP 2: TRANSFER TH SHIP</strong></div>
                    <div style="flex-grow: 1;">${pickupsHtml || '<em>No pickups needed here.</em>'}</div>
                    ${hasDrops && hasPicks ? `<button id="btn-only-pick" style="margin-top: 10px; width: 100%; cursor: pointer; padding: 5px; background: #004400; color: #fff; border: 1px solid #44ff44; font-weight: bold;">📥 Execute ONLY Pickups</button>` : ''}
                </div>
            </div>

            <div style="display: flex; justify-content: center; gap: 10px; margin-bottom: 5px;">
                <button id="btn-step-prev" style="cursor: pointer; padding: 6px 15px; background: #444; color: #fff; border: 1px solid #777; font-weight: bold;">
                    ⏪ Step Backward
                </button>
                <button id="btn-step-skip" style="cursor: pointer; padding: 6px 15px; background: #555; color: #aaa; border: 1px dashed #777; font-weight: bold;">
                    ⏭️ Skip Location
                </button>
                <button id="btn-step-force" style="cursor: pointer; padding: 6px 15px; background: #004466; color: #88ccff; border: 1px solid #0088ff; font-weight: bold;">
                    ✓ Force Complete (Use Expected Math)
                </button>
            </div>
        `;
        document.body.insertBefore(hud, document.body.firstChild);

        // Split-Transfer Button Logic
        let btnDrop = document.getElementById('btn-only-drop');
        if (btnDrop) {
            btnDrop.addEventListener('click', (e) => {
                e.preventDefault();
                document.querySelectorAll(tradeInputSelectorFor('buy')).forEach(i => i.value = '');
                let btn = document.querySelector('input[type="submit"][value*="Transfer"], input[type="submit"][value*="Trade"], input[name="trade"]');
                if (btn) btn.click();
                else if (document.forms.length > 0) document.forms[document.forms.length-1].submit();
            });
        }

        let btnPick = document.getElementById('btn-only-pick');
        if (btnPick) {
            btnPick.addEventListener('click', (e) => {
                e.preventDefault();
                document.querySelectorAll(tradeInputSelectorFor('sell')).forEach(i => i.value = '');
                let btn = document.querySelector('input[type="submit"][value*="Transfer"], input[type="submit"][value*="Trade"], input[name="trade"]');
                if (btn) btn.click();
                else if (document.forms.length > 0) document.forms[document.forms.length-1].submit();
            });
        }

        const qolBtn = document.getElementById('qol-next-btn');
        if (qolBtn) {
            qolBtn.addEventListener('click', () => {
                const statusEl = document.getElementById('qol-status');
                if (statusEl) statusEl.innerText = qolDescribeNextStep();
                qolNextStep();
                if (statusEl) statusEl.innerText = qolDescribeNextStep();
            });
        }

        bindQolAutoButtons();
        bindQolHotkey();
        if (GM_getValue('logistics_auto_step', false)) {
            if (hasSpaceError) {
                GM_setValue('logistics_needs_recalc', true);
                __perfMark('qol_next');
                __perfMark('nav_return_click');
                GM_deleteValue('logistics_trade_loc');
                try { top.frames.main.location.href = '//app/main?nav=1'; }
                catch (err) { top.location.href = '//app/main?nav=1'; }
                return;
            }
            const inputs = Array.from(document.querySelectorAll(allTradeInputSelector()));
            const hasSell = inputs.some(i => classifyTradeInput(i) === 'sell' && parseInt(i.value, 10) > 0);
            const hasBuy = inputs.some(i => classifyTradeInput(i) === 'buy' && parseInt(i.value, 10) > 0);
            if (hasSell || hasBuy) {
                __perfMark('qol_next');
                __perfMark('trade_post_click');
                const btn = document.querySelector('input[type="submit"][value*="Transfer"], input[type="submit"][value*="Trade"], input[name="trade"]');
                if (btn) btn.click();
                else if (document.forms.length > 0) document.forms[document.forms.length - 1].submit();
            } else {
                __perfMark('qol_next');
                __perfMark('nav_return_click');
                GM_deleteValue('logistics_trade_loc');
                try { top.frames.main.location.href = '//app/main?nav=1'; }
                catch (err) { top.location.href = '//app/main?nav=1'; }
            }
            return;
        }
        autoStepResume();

        document.getElementById('btn-step-force').addEventListener('click', () => {
            let state = GM_getValue('raw_bookkeeper_data', []);
            let node = state.find(n => normalizeCoords(n.location) === normalizeCoords(currentStep.location));

            let liveStr = GM_getValue('logistics_live_cargo', '');
            let liveCargo = parseLiveCargo(liveStr);

            Object.entries(currentStep.dropoffs || {}).forEach(([name, data]) => {
                let key = name.toLowerCase();

                liveCargo[key] = (liveCargo[key] || 0) - data.amount;
                if (liveCargo[key] <= 0) delete liveCargo[key];

                if (node && node.dropoffs) {
                    let nodeKey = Object.keys(node.dropoffs).find(k => k.toLowerCase() === key);
                    if (nodeKey) {
                        node.dropoffs[nodeKey].amount -= data.amount;
                        if (node.dropoffs[nodeKey].amount <= 0) delete node.dropoffs[nodeKey];
                    }
                }
            });

            Object.entries(currentStep.pickups || {}).forEach(([name, data]) => {
                let key = name.toLowerCase();

                liveCargo[key] = (liveCargo[key] || 0) + data.amount;

                if (node && node.pickups) {
                    let nodeKey = Object.keys(node.pickups).find(k => k.toLowerCase() === key);
                    if (nodeKey) {
                        node.pickups[nodeKey].amount -= data.amount;
                        if (node.pickups[nodeKey].amount <= 0) delete node.pickups[nodeKey];
                    }
                }
            });

            GM_setValue('logistics_live_cargo', stringifyLiveCargo(liveCargo));
            GM_setValue('raw_bookkeeper_data', state);

            activeData.history = activeData.history || [];
            activeData.history.push(currentStep);
            activeData.steps.shift();
            GM_setValue('logistics_route_v5', activeData);
            GM_setValue('logistics_needs_recalc', true);
            window.location.href = '/app/main';
        });

        document.getElementById('btn-step-skip').addEventListener('click', () => {
            activeData.history = activeData.history || [];
            activeData.history.push({ ...currentStep, skipped: true, oldPickups: currentStep.pickups, oldDropoffs: currentStep.dropoffs });

            let state = GM_getValue('raw_bookkeeper_data', []);
            let idx = state.findIndex(n => normalizeCoords(n.location) === normalizeCoords(currentStep.location));
            if (idx !== -1) {
                state[idx].pickups = {};
                state[idx].dropoffs = {};
                GM_setValue('raw_bookkeeper_data', state);
            }

            activeData.steps.shift();
            GM_setValue('logistics_route_v5', activeData);
            GM_setValue('logistics_needs_recalc', true);
            window.location.href = '/app/main';
        });

        document.getElementById('btn-step-prev').addEventListener('click', () => {
            activeData.history = activeData.history || [];
            if (activeData.history.length === 0) {
                alert("No previous steps in memory to rewind.");
                return;
            }
            let prev = activeData.history.pop();
            let state = GM_getValue('raw_bookkeeper_data', []);
            let idx = state.findIndex(n => n.location === prev.location);

            let liveStr = GM_getValue('logistics_live_cargo', '');
            let liveCargo = parseLiveCargo(liveStr);

            if (prev.skipped) {
                if (idx !== -1) {
                    state[idx].pickups = prev.oldPickups || {};
                    state[idx].dropoffs = prev.oldDropoffs || {};
                }
            } else {
                Object.entries(prev.dropoffs || {}).forEach(([name, data]) => {
                    let key = name.toLowerCase();

                    liveCargo[key] = (liveCargo[key] || 0) + data.amount;

                    if (idx !== -1) {
                        let nodeKey = Object.keys(state[idx].dropoffs).find(k => k.toLowerCase() === key);
                        if (!nodeKey) { nodeKey = name; state[idx].dropoffs[nodeKey] = { amount: 0, id: data.id }; }
                        state[idx].dropoffs[nodeKey].amount += data.amount;
                    }
                });

                Object.entries(prev.pickups || {}).forEach(([name, data]) => {
                    let key = name.toLowerCase();

                    liveCargo[key] = (liveCargo[key] || 0) - data.amount;
                    if (liveCargo[key] <= 0) delete liveCargo[key];

                    if (idx !== -1) {
                        let nodeKey = Object.keys(state[idx].pickups).find(k => k.toLowerCase() === key);
                        if (!nodeKey) { nodeKey = name; state[idx].pickups[nodeKey] = { amount: 0, id: data.id }; }
                        state[idx].pickups[nodeKey].amount += data.amount;
                    }
                });
            }

            GM_setValue('logistics_live_cargo', stringifyLiveCargo(liveCargo));
            GM_setValue('raw_bookkeeper_data', state);
            activeData.steps.unshift(prev);
            GM_setValue('logistics_route_v5', activeData);
            GM_setValue('logistics_needs_recalc', true);
            location.reload();
                });
    }

    // --- 17. Main Nav Screen: Draggable Control Center ---
    function injectDraggableUI() {
        const uiPos = GM_getValue('logistics_ui_pos', { top: '50px', left: '50px' });

        const container = document.createElement('div');
        container.id = 'logistics-drag-ui';
        container.style.cssText = `
            position: absolute; top: ${uiPos.top}; left: ${uiPos.left}; width: 280px;
            background-color: #00001C; border: 1px solid #555; font-family: Verdana, sans-serif;
            font-size: 11px; color: #ccc; z-index: 9999; box-shadow: 2px 2px 10px rgba(0,0,0,0.8);
        `;

        let savedHubCoords = GM_getValue('config_hub_coords', '');
        let savedMaxCargo = GM_getValue('config_max_cargo', '200');
        let savedHubType = GM_getValue('config_hub_type', 'station');
        let savedToCoords = GM_getValue('config_to_coords', '');
        let savedToCap = GM_getValue('config_to_cap', '');
        let savedMinTrade = GM_getValue('config_min_trade', '25');
        let savedExports = GM_getValue('config_export_items', '');
        let savedTakeAllItems = GM_getValue('config_take_all_items', '');
        let savedLiveCargo = GM_getValue('logistics_live_cargo', '');
        let savedAutoRetreat = GM_getValue('config_auto_retreat', true);

        const activeData = GM_getValue('logistics_route_v5', { steps: [], toInventory: {}, history: [] });
        const safeSteps = activeData.steps || [];
        const safeToInventory = activeData.toInventory || {};

        // Per-step credit/AP economics. Computed once from the trade-tracker
        // store + terrain equip_f so the itinerary can show profit, AP
        // spent, and credit-per-AP ratio for every stop, plus a running
        // cumulative total across the whole route. Wrapped in try/catch so a
        // failure in economics (e.g. missing map data) never breaks the UI.
        let econ = [];
        let anyUntracked = false;
        try {
            econ = computeRouteEconomics(safeSteps);
            for (const e of econ) { if (!e.isTo && !e.hasPriceData) anyUntracked = true; }
        } catch (err) {
            console.error('[logistics-econ] computeRouteEconomics failed:', err);
        }

        // fmtCr / fmtRatio are shared top-level helpers declared in the
        // exports-calculator part (function declarations hoist IIFE-wide).
        function profitColor(p) { return p < 0 ? '#ff5555' : (p > 0 ? '#88ff88' : '#888'); }

        let routeHtml = '';
        if (safeSteps.length === 0) {
            routeHtml = `<div style="color: #888; text-align: center;">No active route simulated.</div>`;
        } else {
            safeSteps.forEach((step, index) => {
                let pickups = Object.entries(step.pickups || {}).map(([name, data]) => `${data.amount} ${name}`).join(', ');
                let dropoffs = Object.entries(step.dropoffs || {}).map(([name, data]) => `${data.amount} ${name}`).join(', ');

                let isHub = step.name.includes("Primary Hub");
                let colorBorder = isHub ? "#ff4444" : "#333";

                // Economics line for this step.
                const e = econ[index] || {};
                const stepAp = e.apCost != null ? e.apCost : '?';
                const hasPrice = !!e.hasPriceData;
                const isTo = !!e.isTo;
                const profitTxt = isTo
                    ? '<span style="color:#666;">stash</span>'
                    : (hasPrice
                        ? `<span style="color:${profitColor(e.profit)};">${e.profit >= 0 ? '+' : ''}${fmtCr(e.profit)} cr</span>`
                        : '<span style="color:#666;">no price</span>');
                const ratioTxt = (hasPrice && e.ratio != null)
                    ? `<span style="color:#00ff88;">${fmtRatio(e.ratio)}</span>`
                    : '<span style="color:#666;">?</span>';
                const cumProfitTxt = `<span style="color:${profitColor(e.cumProfit)};">${e.cumProfit >= 0 ? '+' : ''}${fmtCr(e.cumProfit)} cr</span>`;
                const cumRatioTxt = (e.cumRatio != null)
                    ? `<span style="color:#00ddaa;">${fmtRatio(e.cumRatio)}</span>`
                    : '<span style="color:#666;">?</span>';
                const partialTag = e.partial ? ' <span style="color:#cc8844;">(partial)</span>' : '';

                routeHtml += `<div style="border-bottom: 1px dashed ${colorBorder}; padding-bottom: 4px; margin-bottom: 4px; font-size: 10px;">
                    <strong style="color: ${isHub ? '#ff8888' : '#ddd'};">#${index + 1} ${step.location}</strong> - ${step.name}<br>
                    <div style="padding-left: 10px;">
                        ${pickups ? `<span style="color: #55ff55;">⬆ Pick up: ${pickups}</span><br>` : ''}
                        ${dropoffs ? `<span style="color: #ff5555;">⬇ Drop off: ${dropoffs}</span><br>` : ''}
                    </div>
                    <div style="padding-left: 10px; color: #aaa; border-top: 1px dotted #222; margin-top: 2px; padding-top: 2px;">
                        <span style="color:#ffaa44;">AP ${stepAp}</span> ·
                        profit ${profitTxt} ·
                        cr/AP ${ratioTxt}${partialTag}
                        <span style="color:#555;"> | </span>
                        <span style="color:#88ccff;">Σ</span>
                        AP ${e.cumAp != null ? e.cumAp : '?'} ·
                        profit ${cumProfitTxt} ·
                        cr/AP ${cumRatioTxt}
                    </div>
                </div>`;
            });

            let toDepositStr = Object.entries(safeToInventory).map(([name, qty]) => `${qty} ${name}`).join(', ');
            if (toDepositStr) {
                routeHtml += `<div style="background: #002233; padding: 4px; border: 1px solid #0088ff; margin-top: 6px; color: #88ccff; font-size: 10px;">
                    <strong>TH STASH:</strong> ${toDepositStr}
                </div>`;
            }

            if (anyUntracked) {
                routeHtml += `<div style="color: #8a6a3a; font-size: 9px; margin-top: 4px;">⚠ Some stops have no captured price data (shown as "no price"). Open their trade screens to capture prices. Untracked steps count as 0 profit in the cumulative total.</div>`;
            }
        }

        container.innerHTML = `
            <div id="logistics-drag-header" style="background-image: url('//static.example.com/img/std/text2.png'); padding: 4px; font-weight: bold; color: #ddd; border-bottom: 1px solid #555; cursor: move; display: flex; justify-content: space-between;">
                <span>Logistics Sim V6.58</span>
                <span id="logistics-min-btn" style="cursor: pointer; color: #aaa;">[-]</span>
            </div>
            <div id="logistics-drag-body" style="padding: 8px; display: flex; flex-direction: column; gap: 6px;">

                <div style="border: 1px solid #00ff00; background: #001100; padding: 6px; margin-bottom: 2px;">
                    <div id="qol-status" style="color: #00ff00; font-weight: bold; font-size: 11px; margin-bottom: 4px; text-align: center; min-height: 14px;">${qolDescribeNextStep()}</div>
                    <button id="qol-next-btn" style="width: 100%; cursor: pointer; padding: 6px; background: #004400; color: #fff; border: 1px solid #0f0; font-weight: bold; font-size: 12px;">\u25b6 Next Step</button>
                    <div style="display: flex; gap: 4px; margin-top: 4px;">
                        <button id="qol-auto-btn" style="flex: 1; cursor: pointer; padding: 4px; background: #003a00; color: #88ff88; border: 1px solid #0f0; font-weight: bold; font-size: 11px;">\u23a9 Auto Run</button>
                        <button id="qol-stop-btn" disabled style="flex: 1; cursor: pointer; padding: 4px; background: #3a0000; color: #ff8888; border: 1px solid #f00; font-weight: bold; font-size: 11px; opacity: 0.5;">\u23cf Stop</button>
                    </div>
                </div>

                <div style="display: flex; align-items: center; gap: 4px; margin-top: 2px;">
                    <input type="checkbox" id="nav-auto-retreat" ${savedAutoRetreat ? 'checked' : ''} style="cursor: pointer;">
                    <label for="nav-auto-retreat" style="color: #88ccff; font-size: 10px; cursor: pointer;" title="Auto-retreat when ambushed by cloaked/hidden NPCs during auto-fly, then resume the flight.">Auto-retreat from ambush</label>
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <input type="text" id="nav-hub-coords" value="${savedHubCoords}" style="width: 50px; background: #111; color: #0f0; border: 1px solid #444;">
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <label>Hub Type:</label>
                    <select id="nav-hub-type" style="width: 120px; background: #111; color: #0f0; border: 1px solid #444;">
                        <option value="station" ${savedHubType === 'station' ? 'selected' : ''}>Station</option>
                        <option value="class_a" ${savedHubType === 'class_a' ? 'selected' : ''}>Class A Station</option>
                        <option value="class_m" ${savedHubType === 'class_m' ? 'selected' : ''}>Class M Station</option>
                        <option value="class_i" ${savedHubType === 'class_i' ? 'selected' : ''}>Class I Station</option>
                        <option value="class_r" ${savedHubType === 'class_r' ? 'selected' : ''}>Class R Station</option>
                        <option value="none" ${savedHubType === 'none' ? 'selected' : ''}>Empty TO</option>
                    </select>
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <label title="Your base Safe Transport limit">Safe Cargo Limit:</label>
                    <input type="number" id="nav-max-cargo" value="${savedMaxCargo}" style="width: 50px; background: #111; color: #0f0; border: 1px solid #444;">
                </div>

                <hr style="border: 0; border-top: 1px dashed #333; margin: 2px 0;">

                <div style="display: flex; justify-content: space-between;">
                    <label style="color: #88ccff;">TH Coords:</label>
                    <input type="text" id="nav-to-coords" value="${savedToCoords}" style="width: 50px; background: #111; color: #88ccff; border: 1px solid #444;">
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <label style="color: #88ccff;">TH Space:</label>
                    <input type="number" id="nav-to-cargo" value="${savedToCap}" style="width: 50px; background: #111; color: #88ccff; border: 1px solid #444;">
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <label style="color: #ffaa55;" title="Ignore trades smaller than this">Min Trade Vol:</label>
                    <input type="number" id="nav-min-trade" value="${savedMinTrade}" style="width: 50px; background: #111; color: #ffaa55; border: 1px solid #444;">
                </div>

                <div style="display: flex; justify-content: space-between;">
                    <label style="color: #ffaa55;" title="Comma separated. Items here will be extracted to TH.">Exports:</label>
                    <input type="text" id="nav-export-items" value="${savedExports}" placeholder="Robots, Optics..." style="width: 140px; background: #111; color: #ffaa55; border: 1px solid #444;">
                </div>

                <hr style="border: 0; border-top: 1px dashed #333; margin: 2px 0;">

                <div style="display: flex; justify-content: space-between;">
                    <label style="color: #ffff55;" title="Auto-updates via Nav screen.">Live Ship Cargo:</label>
                    <input type="text" id="nav-live-cargo" value="${savedLiveCargo}" style="width: 140px; background: #111; color: #ffff55; border: 1px solid #444;" readonly>
                </div>

                <div style="display: flex; gap: 4px; align-items: center; margin-top: 4px;">
                    <input type="text" id="nav-takeall-items" value="${savedTakeAllItems}" placeholder="Items to gather..." style="flex: 1; background: #111; color: #ff88ff; border: 1px solid #444;">
                    <button id="nav-btn-takeall" style="cursor: pointer; padding: 4px; background: #420044; color: #fff; border: 1px solid #f0f;">Take All</button>
                </div>

                <div style="display: flex; gap: 4px; align-items: center; margin-top: 4px;">
                    <span style="flex: 1; color: #ffaa55; font-size: 11px;">Sell all cargo to highest-priced buyers (this sector)</span>
                    <button id="nav-btn-dumpall" style="cursor: pointer; padding: 4px; background: #4a3a00; color: #fff; border: 1px solid #ffa500;">Dump All</button>
                </div>

                <div style="display: flex; justify-content: space-between; margin-top: 4px;">
                    <button id="nav-btn-sim" style="cursor: pointer; padding: 4px; background: #004400; color: #fff; border: 1px solid #0f0; flex-grow: 1; margin-right: 2px;">Sync & Sim</button>
                    <button id="nav-btn-clear" style="cursor: pointer; padding: 4px; background: #422; color: #ccc; border: 1px solid #555;">Clear Route</button>
                </div>

                <div style="margin-top: 4px;">
                    <button id="nav-btn-toggle-route" style="width: 100%; cursor: pointer; padding: 3px; background: #222; color: #aaa; border: 1px solid #444;">[ Toggle Route Itinerary ]</button>
                </div>
                <div id="nav-full-route-display" style="display: none; max-height: 180px; overflow-y: auto; background-color: #0b0b14; border: 1px solid #333; padding: 6px;">
                    ${routeHtml}
                </div>
            </div>
        `;
        document.body.appendChild(container);

        const header = document.getElementById('logistics-drag-header');
        let isDragging = false, startX, startY, initialX, initialY;

        header.addEventListener('mousedown', (e) => {
            if(e.target.id === 'logistics-min-btn') return;
            isDragging = true;
            startX = e.clientX; startY = e.clientY;
            initialX = container.offsetLeft; initialY = container.offsetTop;
        });

        document.addEventListener('mousemove', (e) => {
            if (!isDragging) return;
            let dx = e.clientX - startX;
            let dy = e.clientY - startY;
            container.style.left = (initialX + dx) + 'px';
            container.style.top = (initialY + dy) + 'px';
        });

        document.addEventListener('mouseup', () => {
            if (isDragging) {
                isDragging = false;
                GM_setValue('logistics_ui_pos', { top: container.style.top, left: container.style.left });
            }
        });

        document.getElementById('logistics-min-btn').addEventListener('click', () => {
            const body = document.getElementById('logistics-drag-body');
            const btn = document.getElementById('logistics-min-btn');
            if (body.style.display === 'none') {
                body.style.display = 'flex';
                btn.innerText = '[-]';
            } else {
                body.style.display = 'none';
                btn.innerText = '[+]';
            }
        });

        document.getElementById('nav-btn-toggle-route').addEventListener('click', () => {
            const disp = document.getElementById('nav-full-route-display');
            disp.style.display = disp.style.display === 'none' ? 'block' : 'none';
        });

        const autoRetreatChk = document.getElementById('nav-auto-retreat');
        if (autoRetreatChk) {
            autoRetreatChk.addEventListener('change', (e) => {
                GM_setValue('config_auto_retreat', e.target.checked);
            });
        }

        document.getElementById('nav-btn-sim').addEventListener('click', () => {
            GM_setValue('config_hub_coords', normalizeCoords(document.getElementById('nav-hub-coords').value));
            GM_setValue('config_hub_type', document.getElementById('nav-hub-type').value);
            GM_setValue('config_max_cargo', document.getElementById('nav-max-cargo').value);
            GM_setValue('config_to_coords', normalizeCoords(document.getElementById('nav-to-coords').value));
            GM_setValue('config_to_cap', document.getElementById('nav-to-cargo').value);
            GM_setValue('config_min_trade', document.getElementById('nav-min-trade').value);
            GM_setValue('config_export_items', document.getElementById('nav-export-items').value);

            GM_setValue('logistics_auto_sim', true);
            window.location.href = '/app/overview';
        });

        document.getElementById('nav-btn-takeall').addEventListener('click', () => {
            GM_setValue('config_hub_coords', normalizeCoords(document.getElementById('nav-hub-coords').value));
            GM_setValue('config_max_cargo', document.getElementById('nav-max-cargo').value);
            GM_setValue('config_to_coords', normalizeCoords(document.getElementById('nav-to-coords').value));
            GM_setValue('config_to_cap', document.getElementById('nav-to-cargo').value);
            GM_setValue('config_take_all_items', document.getElementById('nav-takeall-items').value);
            GM_setValue('logistics_take_all_mode', true);
            window.location.href = '/app/overview';
        });

        document.getElementById('nav-btn-dumpall').addEventListener('click', () => {
            GM_setValue('config_hub_coords', normalizeCoords(document.getElementById('nav-hub-coords').value));
            GM_setValue('config_max_cargo', document.getElementById('nav-max-cargo').value);
            GM_setValue('config_to_coords', normalizeCoords(document.getElementById('nav-to-coords').value));
            GM_setValue('config_to_cap', document.getElementById('nav-to-cargo').value);
            GM_setValue('logistics_dump_all_mode', true);
            window.location.href = '/app/overview';
        });

        document.getElementById('nav-btn-clear').addEventListener('click', () => {
            GM_setValue('logistics_route_v5', { steps: [], toInventory: {}, history: [] });
            GM_setValue('logistics_live_cargo', '');
            GM_setValue('raw_bookkeeper_data', []);
            GM_deleteValue('logistics_ship_space');
            GM_deleteValue('logistics_mag_scoop_used');
            location.reload();
        });

        document.getElementById('qol-next-btn').addEventListener('click', () => {
            const statusEl = document.getElementById('qol-status');
            if (statusEl) statusEl.innerText = qolDescribeNextStep();
            qolNextStep();
            if (statusEl) statusEl.innerText = qolDescribeNextStep();
        });

        bindQolAutoButtons();
        bindQolHotkey();
        autoStepResume();
    }

    // --- 18. Fly Here Panel ---

    function injectFlyHerePanel() {
        const uiPos = GM_getValue('flyhere_ui_pos', { top: '50px', right: '6px' });

        const wrap = document.createElement('div');
        wrap.id = 'logistics-flyhere-panel';
        wrap.style.cssText = [
            'position:absolute',
            'top:' + uiPos.top,
            (uiPos.left != null ? 'left:' + uiPos.left : 'right:' + (uiPos.right || '6px')),
            'width:260px',
            'background-color:#00001C',
            'border:1px solid #0088ff',
            'font-family:Verdana,sans-serif',
            'font-size:10px',
            'color:#ccc',
            'z-index:9998',
            'box-shadow:2px 2px 10px rgba(0,0,0,0.8)'
        ].join(';');

        const header = document.createElement('div');
        header.style.cssText = 'background:#003355;padding:5px 7px;cursor:move;font-weight:bold;color:#88ccff;border-bottom:1px solid #0088ff;user-select:none;display:flex;justify-content:space-between;align-items:center;';
        header.innerHTML = '<span>\u2708 Fly Here</span><span id="flyhere-min-btn" style="cursor:pointer;color:#88ccff;">[-]</span>';
        wrap.appendChild(header);

        const body = document.createElement('div');
        body.id = 'flyhere-body';
        body.style.cssText = 'padding:6px 7px;display:flex;flex-direction:column;gap:5px;';
        wrap.appendChild(body);

        // >> Search input — filters the sector list as you type.
        const searchInput = document.createElement('input');
        searchInput.type = 'text';
        searchInput.placeholder = 'search sectors...';
        searchInput.style.cssText = 'width:100%;box-sizing:border-box;background:#111;color:#88ccff;border:1px solid #0088ff;font-size:10px;padding:2px 4px;';
        body.appendChild(searchInput);

        // >> Sector list (filtered listbox). A size=8 select gives a
        // scrollable, searchable list of all ~250 sectors from SECTOR_DATA.
        const sectorSelect = document.createElement('select');
        sectorSelect.size = 8;
        sectorSelect.style.cssText = 'width:100%;box-sizing:border-box;background:#111;color:#88ccff;border:1px solid #0088ff;font-size:10px;padding:2px;';
        body.appendChild(sectorSelect);

        // >> Sector info — shows selected sector's grid dimensions and the
        // valid X/Y coord range so the user knows what coordinates to enter.
        const infoDiv = document.createElement('div');
        infoDiv.style.cssText = 'color:#666;font-size:9px;min-height:12px;';
        body.appendChild(infoDiv);

        // >> Coord inputs — separate X / Y number fields (clearer than a
        // single "[x,y]" text field and matches the panel's form style).
        const coordRow = document.createElement('div');
        coordRow.style.cssText = 'display:flex;gap:4px;align-items:center;';
        const xLabel = document.createElement('label');
        xLabel.style.cssText = 'color:#aaa;width:14px;';
        xLabel.textContent = 'X';
        coordRow.appendChild(xLabel);
        const xInput = document.createElement('input');
        xInput.type = 'number';
        xInput.min = '0';
        xInput.style.cssText = 'width:55px;background:#111;color:#0f0;border:1px solid #444;font-size:10px;padding:2px;';
        coordRow.appendChild(xInput);
        const yLabel = document.createElement('label');
        yLabel.style.cssText = 'color:#aaa;width:14px;margin-left:6px;';
        yLabel.textContent = 'Y';
        coordRow.appendChild(yLabel);
        const yInput = document.createElement('input');
        yInput.type = 'number';
        yInput.min = '0';
        yInput.style.cssText = 'width:55px;background:#111;color:#0f0;border:1px solid #444;font-size:10px;padding:2px;';
        coordRow.appendChild(yInput);
        body.appendChild(coordRow);

        // >> Status display — shows the plotted path summary or errors.
        const statusDiv = document.createElement('div');
        statusDiv.style.cssText = 'color:#aaa;font-size:9px;min-height:26px;padding:3px;border:1px dashed #222;line-height:1.4;';
        body.appendChild(statusDiv);

        // >> Buttons: Plot Path & AP  +  Fly
        const btnRow = document.createElement('div');
        btnRow.style.cssText = 'display:flex;gap:4px;';
        const plotBtn = document.createElement('button');
        plotBtn.type = 'button';
        plotBtn.textContent = 'Plot Path & AP';
        plotBtn.style.cssText = 'flex:1;cursor:pointer;font-size:10px;background:#332200;color:#ffaa55;border:1px solid #aa7744;padding:4px;';
        const flyBtn = document.createElement('button');
        flyBtn.type = 'button';
        flyBtn.textContent = '\u2708 Fly';
        flyBtn.disabled = true;
        flyBtn.style.cssText = 'flex:1;cursor:pointer;font-size:10px;background:#003300;color:#88ff88;border:1px solid #0f0;padding:4px;opacity:0.5;';
        btnRow.appendChild(plotBtn);
        btnRow.appendChild(flyBtn);
        body.appendChild(btnRow);

        // >> Ship config (collapsible) — drive, nav, stims, equip_f, flux,
        // equip_d, wormhole cost & seal.  Stored in GM_setValue as
        // config_ship_* so the equip_f's getShipOptions() picks them up.
        const shipCfg = document.createElement('details');
        shipCfg.style.cssText = 'margin-top:2px;border:1px solid #222;padding:2px;';
        const shipSummary = document.createElement('summary');
        shipSummary.textContent = 'Ship config';
        shipSummary.style.cssText = 'cursor:pointer;color:#88ccff;font-size:9px;';
        shipCfg.appendChild(shipSummary);
        const shipBody = document.createElement('div');
        shipBody.style.cssText = 'display:grid;grid-template-columns:1fr 1fr;gap:2px;margin-top:3px;font-size:9px;';

        function shipNum(id, label, val, min, max) {
            const wrap = document.createElement('div');
            wrap.style.cssText = 'display:flex;align-items:center;gap:2px;';
            const lbl = document.createElement('span');
            lbl.textContent = label; lbl.style.cssText = 'color:#888;width:42px;';
            const inp = document.createElement('input');
            inp.type = 'number'; inp.id = 'shipcfg-' + id; inp.value = val;
            if (min != null) inp.min = min; if (max != null) inp.max = max;
            inp.style.cssText = 'width:38px;background:#111;color:#0f0;border:1px solid #444;font-size:9px;padding:1px;';
            wrap.appendChild(lbl); wrap.appendChild(inp); shipBody.appendChild(wrap);
            return inp;
        }
        function shipSel(id, label, val, opts) {
            const wrap = document.createElement('div');
            wrap.style.cssText = 'display:flex;align-items:center;gap:2px;';
            const lbl = document.createElement('span');
            lbl.textContent = label; lbl.style.cssText = 'color:#888;width:42px;';
            const sel = document.createElement('select');
            sel.id = 'shipcfg-' + id;
            sel.style.cssText = 'width:60px;background:#111;color:#0f0;border:1px solid #444;font-size:9px;padding:1px;';
            for (const o of opts) {
                const op = document.createElement('option');
                op.value = o[0]; op.textContent = o[1];
                if (String(val) === String(o[0])) op.selected = true;
                sel.appendChild(op);
            }
            wrap.appendChild(lbl); wrap.appendChild(sel); shipBody.appendChild(wrap);
            return sel;
        }
        function shipChk(id, label, checked) {
            const wrap = document.createElement('div');
            wrap.style.cssText = 'display:flex;align-items:center;gap:2px;';
            const cb = document.createElement('input');
            cb.type = 'checkbox'; cb.id = 'shipcfg-' + id; cb.checked = !!checked;
            cb.style.cssText = 'cursor:pointer;';
            const lbl = document.createElement('span');
            lbl.textContent = label; lbl.style.cssText = 'color:#888;font-size:9px;cursor:pointer;';
            lbl.addEventListener('click', () => { cb.checked = !cb.checked; cb.dispatchEvent(new Event('change')); });
            wrap.appendChild(cb); wrap.appendChild(lbl); shipBody.appendChild(wrap);
            return cb;
        }

        const sOpt = getShipOptions();
        const eDrive    = shipNum('drive', 'Drive', sOpt.drive_speed, 0, 10);
        const eNav      = shipSel('nav', 'Nav', sOpt.navigation_level, [[0,'0'],[1,'1'],[2,'2'],[3,'3']]);
        const eAmber    = shipChk('amber', 'Amber', sOpt.equip_e);
        const ePF       = shipSel('pf', 'Path', sOpt.equip_f, [['none','none'],['primary','pri'],['secondary','sec']]);
        const eBoost    = shipChk('boost', 'Boost', sOpt.boost);
        const eequip_a  = shipChk('equip_a', 'equip_a', sOpt.equip_a);
        const eGasF     = shipSel('gasflux', 'GasFx', sOpt.equip_b, [['none','none'],['weak','wk'],['strong','str']]);
        const eEnF      = shipSel('enflux', 'EnFx', sOpt.equip_c, [['none','none'],['weak','wk'],['strong','str']]);
        const eVP       = shipSel('vp', 'VPers', sOpt.equip_d, [[0,'0'],[1,'1'],[2,'2']]);
        const eWHC      = shipNum('whcost', 'WH AP', sOpt.wormhole_cost, 0, 50);
        const eSeal     = shipSel('seal', 'Seal', sOpt.wormhole_seal,
            [['none','none'],['seal_a','seal_a'],['seal_b','seal_b'],['seal_c','seal_c'],
             ['wh-closed-A','WH_A off'],['wh-closed-B','WH_B off'],
             ['wh-closed-C','WH_C off'],['wh-closed-D','WH_D off']]);

        // Save on change.
        const cfgMap = [
            [eDrive, 'config_ship_drive_speed', Number],
            [eNav, 'config_ship_navigation_level', v => Number(v)],
            [eAmber, 'config_ship_equip_e', v => !!v],
            [ePF, 'config_ship_equip_f', v => v],
            [eBoost, 'config_ship_boost', v => !!v],
            [eequip_a, 'config_ship_equip_a', v => !!v],
            [eGasF, 'config_ship_equip_b', v => v],
            [eEnF, 'config_ship_equip_c', v => v],
            [eVP, 'config_ship_equip_d', v => Number(v)],
            [eWHC, 'config_ship_wormhole_cost', Number],
            [eSeal, 'config_ship_wormhole_seal', v => v],
        ];
        for (const [el, key, conv] of cfgMap) {
            el.addEventListener('change', () => {
                GM_setValue(key, conv(el.type === 'checkbox' ? el.checked : el.value));
                // Invalidate terrain cache so next path uses new costs.
                _terrainAPCacheKey = null;
            });
        }

        shipCfg.appendChild(shipBody);
        body.appendChild(shipCfg);

        // >> Sector list population & filtering
        let allSectors = [];
        try { allSectors = Object.keys(SECTOR_DATA).sort(); } catch (e) { allSectors = []; }

        function updateSectorInfo() {
            const sd = getSectorData(sectorSelect.value);
            if (sd) {
                infoDiv.textContent = sectorSelect.value + ' \u00b7 ' + sd.cols + '\u00d7' + sd.rows +
                    ' (X:0-' + (sd.cols - 1) + ' Y:0-' + (sd.rows - 1) + ')';
            } else {
                infoDiv.textContent = '';
            }
        }

        function rebuildSectorList(filter) {
            const f = (filter || '').toLowerCase().trim();
            const prev = sectorSelect.value;
            sectorSelect.innerHTML = '';
            let count = 0;
            for (const name of allSectors) {
                if (f && !name.toLowerCase().includes(f)) continue;
                const opt = document.createElement('option');
                opt.value = name;
                opt.textContent = name;
                sectorSelect.appendChild(opt);
                count++;
            }
            // Preserve the previous selection if it survived the filter.
            if (prev && Array.from(sectorSelect.options).some(o => o.value === prev)) {
                sectorSelect.value = prev;
            }
            if (!sectorSelect.value && count > 0) {
                sectorSelect.selectedIndex = 0;
            }
            updateSectorInfo();
        }

        searchInput.addEventListener('input', () => rebuildSectorList(searchInput.value));
        sectorSelect.addEventListener('change', updateSectorInfo);

        // >> Restore saved state / pre-select current sector.
        let savedSector = GM_getValue('flyhere_sector', '');
        let savedX = GM_getValue('flyhere_x', '');
        let savedY = GM_getValue('flyhere_y', '');
        let curSectorName = null;
        try {
            const sel = document.getElementById('sector');
            if (sel) curSectorName = sel.textContent.trim();
        } catch (e) {}
        rebuildSectorList('');
        const initialSector = (curSectorName && allSectors.indexOf(curSectorName) >= 0)
            ? curSectorName
            : (savedSector && allSectors.indexOf(savedSector) >= 0 ? savedSector : (allSectors[0] || ''));
        if (initialSector) sectorSelect.value = initialSector;
        if (savedX !== '') xInput.value = savedX;
        if (savedY !== '') yInput.value = savedY;
        updateSectorInfo();

        // >> Current-position reader (mirrors the nav reading in flyToCoords).
        function getCurrentNavPosition() {
            const coordsEl = document.getElementById('coords');
            const sectorEl = document.getElementById('sector');
            const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
            if (!coordsEl || !sectorEl) return null;
            if (w.userloc === undefined || w.userloc === null) return null;
            const cur = parseCoords(coordsEl.innerText);
            const sectorName = sectorEl.textContent.trim();
            const startTileId = parseInt(w.userloc.toString(), 10);
            if (isNaN(startTileId)) return null;
            return { x: cur.x, y: cur.y, sector: sectorName, tileId: startTileId };
        }

        function setStatus(text, kind) {
            statusDiv.textContent = text;
            statusDiv.style.color = kind === 'err' ? '#ff5555' : (kind === 'ok' ? '#88ff88' : '#aaa');
        }

        let pendingTarget = null;

        function setFlyEnabled(on) {
            flyBtn.disabled = !on;
            flyBtn.style.opacity = on ? '1' : '0.5';
        }

        // >> Plot Path & AP Cost
        // Uses getCrossSectorRoute which handles both same-sector (single
        // leg via local Dijkstra) and cross-sector (multi-leg via wormholes)
        // routing. Displays the total AP cost and wormhole-jump count so the
        // user can confirm the path before committing to the flight.
        plotBtn.addEventListener('click', () => {
            const pos = getCurrentNavPosition();
            if (!pos) { setStatus('Cannot read current position from the nav screen.', 'err'); return; }
            const sector = sectorSelect.value;
            const tx = parseInt(xInput.value, 10);
            const ty = parseInt(yInput.value, 10);
            if (!sector) { setStatus('Select a sector from the list.', 'err'); return; }
            if (isNaN(tx) || isNaN(ty)) { setStatus('Enter valid X and Y coordinates.', 'err'); return; }

            GM_setValue('flyhere_sector', sector);
            GM_setValue('flyhere_x', String(tx));
            GM_setValue('flyhere_y', String(ty));

            if (!parseStaticMap(true)) {
                setStatus('No sector map data in localStorage. Load map_data.txt first.', 'err');
                setFlyEnabled(false);
                pendingTarget = null;
                return;
            }

            const sd = getSectorData(sector);
            if (sd && (tx < 0 || ty < 0 || tx >= sd.cols || ty >= sd.rows)) {
                setStatus('Warning: [' + tx + ',' + ty + '] is out of bounds for ' + sector + ' (' + sd.cols + 'x' + sd.rows + ').', 'err');
            }

            const route = getCrossSectorRoute(pos.sector, pos.tileId, pos.x, pos.y, sector, tx, ty);
            if (!route) {
                setStatus('No path found from ' + pos.sector + ' [' + pos.x + ',' + pos.y + '] to ' + sector + ' [' + tx + ',' + ty + '].', 'err');
                setFlyEnabled(false);
                pendingTarget = null;
                return;
            }

            const legs = route.legs.length;
            const jumps = legs - 1;
            const legTxt = legs === 1
                ? 'same sector'
                : jumps + ' wormhole jump(s), ' + legs + ' legs';
            const fromTxt = (pos.sector === sector) ? '' : ('from ' + pos.sector + ' ');
            setStatus(fromTxt + '\u2192 ' + sector + ' [' + tx + ',' + ty + ']: ' + legTxt + ' \u00b7 ' + route.totalAP + ' AP', 'ok');

            pendingTarget = { x: tx, y: ty, sector: sector, label: sector + ' [' + tx + ',' + ty + ']' };
            setFlyEnabled(true);
        });

        // >> Fly — delegates to flyToCoords (rich nav HUD), which reads the
        // current position itself, builds the route, and drives navAjax one
        // tile at a time with monster/ambush guards. The plot above is only a
        // preview; flyToCoords recomputes the path at flight time so it stays
        // correct even if the ship moved since plotting.
        flyBtn.addEventListener('click', () => {
            if (!pendingTarget) { setStatus('Plot a path first.', 'err'); return; }
            setFlyEnabled(false);
            setStatus('Flying to ' + pendingTarget.label + '...', 'ok');
            const target = pendingTarget;
            flyToCoords(
                { x: target.x, y: target.y, sector: target.sector },
                target.label,
                (arrived) => {
                    setFlyEnabled(true);
                    setStatus(arrived ? 'Arrived at ' + target.label + '.' : 'Flight stopped.', arrived ? 'ok' : 'err');
                }
            );
        });

        // >> Drag logic (header drag to move; click without drag to do nothing)
        let isDragging = false, dragMoved = false, startX = 0, startY = 0, initialX = 0, initialY = 0;
        header.addEventListener('mousedown', (e) => {
            if (e.target.id === 'flyhere-min-btn') return;
            isDragging = true;
            dragMoved = false;
            startX = e.clientX; startY = e.clientY;
            initialX = wrap.offsetLeft; initialY = wrap.offsetTop;
            e.preventDefault();
        });
        document.addEventListener('mousemove', (e) => {
            if (!isDragging) return;
            const dx = e.clientX - startX, dy = e.clientY - startY;
            if (Math.abs(dx) > 3 || Math.abs(dy) > 3) dragMoved = true;
            wrap.style.left = (initialX + dx) + 'px';
            wrap.style.top = (initialY + dy) + 'px';
            wrap.style.right = 'auto';
        });
        document.addEventListener('mouseup', () => {
            if (!isDragging) return;
            isDragging = false;
            if (dragMoved) {
                GM_setValue('flyhere_ui_pos', { top: wrap.style.top, left: wrap.style.left });
            }
        });

        // >> Minimize / expand
        const minBtn = header.querySelector('#flyhere-min-btn');
        minBtn.addEventListener('click', () => {
            if (body.style.display === 'none') {
                body.style.display = 'flex';
                minBtn.textContent = '[-]';
            } else {
                body.style.display = 'none';
                minBtn.textContent = '[+]';
            }
        });

        const mount = document.body || document.documentElement;
        if (mount) mount.appendChild(wrap);
        console.log('[logistics-flyhere] panel injected on', window.location.pathname);
    }

    // --- 19. True AP-Density Simulation Engine ---

    // Resolve the player's current sector from the page's unsafeWindow.userloc
    // so the sim can use the local-sector equip_f's Dijkstra for real
    // terrain-aware AP. Returns null when the page has no userloc or the
    // static map isn't loaded — in that case simTravelAP hard-fails (throws)
    // rather than estimating: a wrong AP value silently corrupts route scoring.
    function simResolveSector() {
        try {
            const w = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
            if (typeof w.userloc === 'undefined' || w.userloc == null) return null;
            const tileId = parseInt(w.userloc, 10);
            if (isNaN(tileId)) return null;
            return getSectorFromTileId(tileId);
        } catch (e) { return null; }
    }

    // Terrain-aware travel AP between two local-sector coords. Routes through
    // HPA* (hpaCrossSectorAP) which resolves fragments independently — so a
    // query from Fragment-B (5,10) to Fragment-A (30,1) correctly
    // routes through the macro wormhole graph instead of a broken merged-grid
    // Dijkstra. NO estimation fallback: throws when the sector is unknown,
    // the static map isn't loaded, or the target is unreachable.
    function simTravelAP(fromCoords, toCoords, sectorName, dijCache) {
        __setOp('simTravelAP');
        if (!fromCoords || !toCoords) {
            throw new Error('simTravelAP: null coords (from=' + JSON.stringify(fromCoords) + ', to=' + JSON.stringify(toCoords) + ')');
        }
        if (!sectorName) {
            throw new Error('simTravelAP: sector unknown (no userloc / static map not loaded)');
        }
        const table = hpaGetTable();
        if (!table) {
            throw new Error('simTravelAP: HPA table unavailable (static map not loaded)');
        }
        const ap = hpaCrossSectorAP(table, sectorName, fromCoords, sectorName, toCoords);
        if (ap === null || !isFinite(ap)) {
            throw new Error('simTravelAP: target ' + toCoords.x + ',' + toCoords.y +
                ' unreachable from ' + fromCoords.x + ',' + fromCoords.y + ' in ' + sectorName);
        }
        return ap;
    }

    // Public cross-sector AP. Memoizes per (fromSec|fromX,fromY|toSec|toX,toY).
    // Delegates to HPA* (hpaCrossSectorAP) which resolves fragments and routes
    // through the pre-compiled macro wormhole graph. Returns Infinity when
    // the target is unreachable (terrain-blocked — a valid routing result).
    // Throws on data errors (null coords, unknown sector, table unavailable).
    function simCrossTravelAP(fromCoords, fromSector, toCoords, toSector, dijCache, crossCache) {
        if (!fromCoords || !toCoords) {
            throw new Error('simCrossTravelAP: null coords (from=' + JSON.stringify(fromCoords) + ', to=' + JSON.stringify(toCoords) + ')');
        }
        if (!fromSector || !toSector) {
            throw new Error('simCrossTravelAP: sector unknown (from=' + fromSector + ', to=' + toSector + ')');
        }
        const key = fromSector + '|' + fromCoords.x + ',' + fromCoords.y + '|' +
                    toSector   + '|' + toCoords.x   + ',' + toCoords.y;
        if (crossCache && crossCache[key] !== undefined) return crossCache[key];
        const table = hpaGetTable();
        if (!table) {
            throw new Error('simCrossTravelAP: HPA table unavailable (static map not loaded)');
        }
        const ap = hpaCrossSectorAP(table, fromSector, fromCoords, toSector, toCoords);
        const result = (ap !== null && isFinite(ap)) ? ap : Infinity;
        if (crossCache) crossCache[key] = result;
        return result;
    }

    // -- Station candidate resolution ---------------------------------------
    // Build a { resId: { name, id } } index from the trade-tracker store.
    // Reused for resolving res_a/res_b/res_c resIds without hardcoding them.
    function simResNameMap() {
        const store = (typeof getTrackerStore === 'function') ? getTrackerStore() : {};
        const map = {};
        for (const k in store) {
            const e = store[k];
            if (!e || !e.commodities) continue;
            for (const rid in e.commodities) {
                const c = e.commodities[rid];
                if (c && c.name) {
                    const key = c.name.toLowerCase();
                    if (!map[key]) map[key] = { id: rid, name: c.name };
                }
            }
        }
        return map;
    }

    // Pull every tracked station whose tile resolves to a known sector+coords.
    // Returns [{ entry, sector, coords }, ...]. The caller filters by sector /
    // AP distance.
    function simGetTrackedStations() {
        const store = (typeof getTrackerStore === 'function') ? getTrackerStore() : {};
        const out = [];
        for (const k in store) {
            const e = store[k];
            if (!e || e.type !== 'station' || e.userloc == null) continue;
            const sector = getSectorFromTileId(e.userloc);
            if (!sector) continue;
            const coords = getLocalCoordsFromTileId(e.userloc, sector);
            if (!coords) continue;
            out.push({ entry: e, sector: sector, coords: coords });
        }
        return out;
    }

    // -- cycle-style profitability evaluation ----------------------------------
    // Given a candidate station, the hub entry, and the ship's current
    // position/sector, compute:
    //   - oneWayAp : AP from currentPos to the station (wormhole-aware)
    //   - returnAp : AP from station back to currentPos (wormhole-aware)
    //   - cycle      : { resABuy, resBBuy, resCBuy, resASell, resBSell,
    //                  resCSell, resAQty, resBQty, resCQty, cost, revenue,
    //                  profit, feasible }
    //     where *Buy/*Sell are trackerProjectBuy/Sell projections; cost and
    //     revenue are summed totalCost / totalRevenue.
    //   - apt     : oneWayAp + returnAp + 10 (two combined trade actions @ 5 AP).
    //   - ratio   : profit / apt   (null if not feasible).
    //
    // The ship buys res_a+res_b (123:84 of maxCargo) at the hub first, travels
    // to the station, sells Res_A/Res_B + buys res_c, returns to currentPos, then
    // the rest of the route can absorb the res_c. Quantities are clamped by
    // actual stock/room at each party.
    function simEvaluatecycleRun(st, hubEntry, currentPos, currentSector, dijCache, crossCache, maxCargo) {
        // Accept either a raw tracker entry (with .userloc, .sector, .coords
        // as a '[x,y]' string) or the {entry, sector, coords:{x,y}} wrapper
        // produced by simGetTrackedStations(). Normalize to the wrapper
        // shape here.
        let stationEntry, stSector, stationCoords;
        if (st && st.entry && st.sector && st.coords && typeof st.coords === 'object') {
            stationEntry = st.entry;
            stSector = st.sector;
            stationCoords = st.coords;
        } else {
            stationEntry = st;
            stSector = st && st.sector;
            stationCoords = st && st.coords ? parseCoords(st.coords) : null;
        }
        const resMap = simResNameMap();
        const resAId   = resMap['res_a']   && resMap['res_a'].id;
        const resBId  = resMap['res_b']  && resMap['res_b'].id;
        const resCId = resMap['res_c'] && resMap['res_c'].id;
        if (!resAId || !resBId || !resCId) return null;
        if (!hubEntry || !hubEntry.commodities) return null;
        if (!hubEntry.commodities[resAId] || !hubEntry.commodities[resBId] || !hubEntry.commodities[resCId]) return null;

        // Station must buy Res_A/Res_B and sell Res_C.
        if (!stationEntry.commodities) return null;
        const stResA = stationEntry.commodities[resAId];
        const stResB = stationEntry.commodities[resBId];
        const stResC = stationEntry.commodities[resCId];
        if (!stResA || !stResB || !stResC) return null;
        if (stResA.sellToObjPrice <= 0 || stResB.sellToObjPrice <= 0 || stResC.buyFromObjPrice <= 0) return null;

        // AP: currentPos -> station, station -> currentPos (wormhole-aware).
        const oneWayAp = simCrossTravelAP(
            currentPos, currentSector,
            { x: stationCoords.x, y: stationCoords.y }, stSector,
            dijCache, crossCache
        );
        const returnAp = simCrossTravelAP(
            { x: stationCoords.x, y: stationCoords.y }, stSector,
            currentPos, currentSector,
            dijCache, crossCache
        );
        if (!isFinite(oneWayAp) || !isFinite(returnAp)) return null;

        // Cargo split: 123:84 of maxCargo.
        const RES_A_RATIO = 123, RES_B_RATIO = 84, RATIO_SUM = RES_A_RATIO + RES_B_RATIO;
        const desiredResA = Math.floor(maxCargo * RES_A_RATIO / RATIO_SUM);
        const desiredResB = Math.floor(maxCargo * RES_B_RATIO / RATIO_SUM);

        // Clamp to actual sellable/buyable volumes.
        const hubResAProj   = trackerProjectBuy(hubEntry, resAId, desiredResA);
        const stResAProj    = trackerProjectSell(stationEntry, resAId, desiredResA);
        const actualResA    = Math.min(hubResAProj ? hubResAProj.quantity : 0,
                                       stResAProj  ? stResAProj.quantity  : 0);
        const hubResBProj  = trackerProjectBuy(hubEntry, resBId, desiredResB);
        const stResBProj   = trackerProjectSell(stationEntry, resBId, desiredResB);
        const actualResB   = Math.min(hubResBProj ? hubResBProj.quantity : 0,
                                       stResBProj  ? stResBProj.quantity  : 0);
        if (actualResA <= 0 && actualResB <= 0) return null;

        // Res_C qty = cargo freed by selling Res_A/Res_B, capped by station stock.
        // We deliberately do NOT also clamp by hub room for selling res_c
        // back: in the resupply cycle the ship carries the res_c onward to the
        // demanding buildings (or sells any excess at whichever of hub /
        // building is more profitable) — requiring the hub to absorb all the
        // res_c up front makes the run infeasible for normal class X/Y
        // stations that don't sell res_c. The station's stock is the only
        // hard constraint.
        const desiredResC = actualResA + actualResB;
        const stResCProj  = trackerProjectBuy(stationEntry, resCId, desiredResC);
        const actualResC  = stResCProj ? stResCProj.quantity : 0;
        if (actualResC <= 0) return null;

        // Re-project with clamped quantities for accurate pricing.
        // (resCSell is left as null — the ship won't sell res_c at the
        // hub unless the hub can buy it; the engine will route excess
        // res_c to whichever of hub/building is more profitable.)
        const resABuy   = trackerProjectBuy(hubEntry, resAId, actualResA);
        const resBBuy  = trackerProjectBuy(hubEntry, resBId, actualResB);
        const resASell  = trackerProjectSell(stationEntry, resAId, actualResA);
        const resBSell = trackerProjectSell(stationEntry, resBId, actualResB);
        const resCBuy = trackerProjectBuy(stationEntry, resCId, actualResC);
        let resCSell = null;
        if (hubEntry.commodities[resCId] && hubEntry.commodities[resCId].sellToObjPrice > 0) {
            resCSell = trackerProjectSell(hubEntry, resCId, actualResC);
        }

        const cost = (resABuy  ? resABuy.totalCost  : 0)
                   + (resBBuy ? resBBuy.totalCost : 0)
                   + (resCBuy ? resCBuy.totalCost : 0);
        const revenue = (resASell   ? resASell.totalRevenue   : 0)
                      + (resBSell  ? resBSell.totalRevenue  : 0)
                      + (resCSell ? resCSell.totalRevenue : 0);
        const profit = revenue - cost;
        const apt = oneWayAp + returnAp + 10;
        const ratio = apt > 0 ? profit / apt : null;
        return {
            st: stationEntry,
            stSector: stSector,
            stationCoords: { x: stationCoords.x, y: stationCoords.y },
            oneWayAp: oneWayAp,
            returnAp: returnAp,
            resAQty: actualResA,
            resBQty: actualResB,
            resCQty: actualResC,
            cost: cost,
            revenue: revenue,
            profit: profit,
            apCost: apt,
            ratio: ratio,
            feasible: profit > 0
        };
    }

    // Local-search improvement over contiguous factory-visit runs in the
    // generated route. Applies two move types iteratively until no further
    // improvement is found:
    //   1. 2-opt: reverse a sub-segment [i..j] — fixes simple crossings.
    //   2. Or-opt: relocate a single step from position i to j — the key move
    //      for pickup-and-delivery problems, where most 2-opt reversals are
    //      cargo-infeasible (picks must precede drops) but individual steps can
    //      often be slid to a geographically better slot without breaking deps.
    // Every candidate move is validated by replaying ship cargo + free space
    // from the run boundary; only moves that stay cargo-feasible are accepted.
    // Hub/TH reload boundaries are never crossed. Only runs with all-unique
    // locations qualify (node-side supply/demand is order-independent).
    function optimizeFactoryRuns(routeSteps, initialCargo, initialSpace, initialAuxHoldUsed, sectorName, startLoc) {
        __setOp('optimizeFactoryRuns');
        if (!routeSteps || routeSteps.length < 3) return routeSteps;
        const dijCache = {};
        const _apCache = new Map();
        const travelAP = (a, b) => {
            const k = a.x + ',' + a.y + '|' + b.x + ',' + b.y;
            const hit = _apCache.get(k);
            if (hit !== undefined) return hit;
            const v = simTravelAP(a, b, sectorName, dijCache);
            _apCache.set(k, v);
            return v;
        };
        // Location cache: parseCoords is pure (same string → same {x,y}), but
        // seqCost/feasibleSeq call locOf on the same steps O(L²·passes) times.
        // Memoize by location string so each [x,y] is parsed once per recalc.
        const _locCache = new Map();
        const locOf = (step) => {
            let p = _locCache.get(step.location);
            if (!p) { p = parseCoords(step.location); _locCache.set(step.location, p); }
            return p;
        };

        function buildSnapshots() {
            const snaps = [];
            let cargo = { ...initialCargo };
            let space = initialSpace;
            let auxHold = initialAuxHoldUsed || 0;
            for (const step of routeSteps) {
                snaps.push({ cargo: { ...cargo }, space, auxHold });
                for (const item in step.dropoffs) {
                    const amt = step.dropoffs[item].amount;
                    const k = item.toLowerCase();
                    cargo[k] = (cargo[k] || 0) - amt;
                    const fromMag = Math.min(amt, auxHold);
                    auxHold -= fromMag;
                    space += (amt - fromMag);
                }
                for (const item in step.pickups) {
                    const amt = step.pickups[item].amount;
                    const k = item.toLowerCase();
                    cargo[k] = (cargo[k] || 0) + amt;
                    space -= amt;
                }
            }
            return snaps;
        }

        function seqCost(seq, inLoc, outLoc) {
            let cost = travelAP(inLoc, locOf(seq[0]));
            for (let k = 0; k + 1 < seq.length; k++) cost += travelAP(locOf(seq[k]), locOf(seq[k + 1]));
            if (outLoc) cost += travelAP(locOf(seq[seq.length - 1]), outLoc);
            return cost;
        }

        function feasibleSeq(seq, startCargo, startSpace, startAuxHold) {
            let cargo = { ...startCargo };
            let space = startSpace;
            let auxHold = startAuxHold || 0;
            for (const step of seq) {
                for (const item in step.dropoffs) {
                    const amt = step.dropoffs[item].amount;
                    const k = item.toLowerCase();
                    if ((cargo[k] || 0) < amt) return false;
                    cargo[k] = (cargo[k] || 0) - amt;
                    const fromMag = Math.min(amt, auxHold);
                    auxHold -= fromMag;
                    space += (amt - fromMag);
                }
                for (const item in step.pickups) {
                    const amt = step.pickups[item].amount;
                    if (space < amt) return false;
                    const k = item.toLowerCase();
                    cargo[k] = (cargo[k] || 0) + amt;
                    space -= amt;
                }
            }
            return true;
        }

        let improved = true;
        let passes = 0;
        while (improved && passes < 40) {
            improved = false;
            passes++;
            let snapshots = buildSnapshots();

            let r = 0;
            while (r < routeSteps.length) {
                if (routeSteps[r].destinationType !== 'factory') { r++; continue; }
                let runEnd = r;
                while (runEnd + 1 < routeSteps.length && routeSteps[runEnd + 1].destinationType === 'factory') runEnd++;
                if (runEnd - r < 1) { r = runEnd + 1; continue; }

                let unique = true;
                const seen = new Set();
                for (let k = r; k <= runEnd; k++) {
                    if (seen.has(routeSteps[k].location)) { unique = false; break; }
                    seen.add(routeSteps[k].location);
                }
                if (!unique) { r = runEnd + 1; continue; }

                const inLoc = r > 0 ? locOf(routeSteps[r - 1]) : startLoc;
                const outStep = (runEnd + 1 < routeSteps.length) ? routeSteps[runEnd + 1] : null;
                const outLoc = outStep ? locOf(outStep) : null;
                const curSeq = routeSteps.slice(r, runEnd + 1);
                const curCost = seqCost(curSeq, inLoc, outLoc);
                const startCargo = snapshots[r].cargo;
                const startSpace = snapshots[r].space;
                const startAuxHold = snapshots[r].auxHold;

                let bestCost = curCost;
                let bestSeq = null;

                // 2-opt: reverse sub-segment [i..j]
                for (let i = 0; i < curSeq.length - 1; i++) {
                    for (let j = i + 1; j < curSeq.length; j++) {
                        let reordered = curSeq.slice();
                        let lo = i, hi = j;
                        while (lo < hi) {
                            const t = reordered[lo]; reordered[lo] = reordered[hi]; reordered[hi] = t;
                            lo++; hi--;
                        }
                        const newCost = seqCost(reordered, inLoc, outLoc);
                        if (newCost >= bestCost) continue;
                        if (!feasibleSeq(reordered, startCargo, startSpace, startAuxHold)) continue;
                        bestCost = newCost;
                        bestSeq = reordered;
                    }
                }

                // Or-opt: relocate single element from index i to index j
                for (let i = 0; i < curSeq.length; i++) {
                    for (let j = 0; j <= curSeq.length; j++) {
                        if (j === i || j === i + 1) continue;
                        let reordered = curSeq.slice();
                        let elem = reordered.splice(i, 1)[0];
                        let insertPos = j > i ? j - 1 : j;
                        reordered.splice(insertPos, 0, elem);
                        const newCost = seqCost(reordered, inLoc, outLoc);
                        if (newCost >= bestCost) continue;
                        if (!feasibleSeq(reordered, startCargo, startSpace, startAuxHold)) continue;
                        bestCost = newCost;
                        bestSeq = reordered;
                    }
                }

                if (bestSeq) {
                    for (let k = 0; k < bestSeq.length; k++) routeSteps[r + k] = bestSeq[k];
                    improved = true;
                    break;
                }
                r = runEnd + 1;
            }
        }
        return routeSteps;
    }

    function calculateOptimalRoute(rawNodes, currentLocStr, hubLocStr, maxCargo, toCoordStr, toCapacity, hubType, minTradeVol, exportItemsStr, liveCargoStr) {
        __setOp('calculateOptimalRoute');
        let routeSteps = [];
        let toInventory = {};

        let shipCargo = parseLiveCargo(liveCargoStr);
        // Protected cargo items are always in the ship (type_a, phantom
        // protection) — they occupy real cargo space but must NEVER be
        // traded, stashed at the TH, or cleared by the cycle override.
        const PROTECTED_CARGO = new Set(['res_fuel', 'phantom protection']);
        // Use auto-detected regular ship capacity if available (excludes aux_hold)
        let autoShipSpace = parseInt(GM_getValue('logistics_ship_space', '0'), 10);
        let maxC = (autoShipSpace > 0 ? autoShipSpace : (parseInt(maxCargo, 10) || 200));
        // Aux_hold items are tracked in the cargo but should not consume regular space
        let auxHoldUsed = parseInt(GM_getValue('logistics_mag_scoop_used', '0'), 10) || 0;
        let shipSpace = maxC;
        for (let amt of Object.values(shipCargo)) {
            shipSpace -= amt;
        }
        shipSpace += auxHoldUsed; // Add back aux_hold items — they don't take regular space
        shipSpace = Math.max(0, shipSpace);

        // Track how many items are in the aux_hold throughout the simulation.
        // When items are dropped off, we drain from the aux_hold first —
        // only the non-aux_hold remainder frees regular shipSpace. This
        // prevents the sim from planning pickups that overflow into the
        // aux_hold (the +150 should never be used for route planning).
        let simAuxHoldUsed = auxHoldUsed;

        let toSpace = parseInt(toCapacity, 10) || 0;
        let minTrade = parseInt(minTradeVol, 10) || 1;
        let exportList = (exportItemsStr || "").split(',').map(s => s.trim().toLowerCase()).filter(s => s.length > 0);

        let simSector = simResolveSector();
        let simDijCache = {};
        let simCrossCache = {}; // memo for simCrossTravelAP across the main loop
        let noStationAvailable = false; // set when cycle search finds no feasible station

        let hasTO = toCoordStr && toCoordStr.match(/\[\d+,\d+\]/) && toSpace > 0;
        let toLoc = hasTO ? parseCoords(toCoordStr) : null;
        let hubLoc = parseCoords(hubLocStr || "[7,16]");
        let currentLoc = parseCoords(currentLocStr || "[7,16]");
        let startLoc = currentLoc;

        let initialShipCargo = JSON.parse(JSON.stringify(shipCargo));
        let initialShipSpace = shipSpace;
        let initialSimAuxHoldUsed = simAuxHoldUsed;

        let unvisited = JSON.parse(JSON.stringify(rawNodes));

        let nameToIdMap = {};
        rawNodes.forEach(n => {
            Object.entries(n.pickups).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
            Object.entries(n.dropoffs).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
        });

        let allowedSupplies = [];
        if (hubType === 'station') allowedSupplies = [];
        else if (hubType === 'class_a') allowedSupplies = ['res_a', 'res_b'];
        else if (hubType === 'class_m') allowedSupplies = ['res_b'];
        else if (hubType === 'class_i') allowedSupplies = ['res_a', 'ore'];
        else if (hubType === 'class_r') allowedSupplies = ['ore'];

        while(true) {
            let remainingDemand = {};
            let unmetHubDemand = {};
            let totalUnmetHubDemand = 0;

            unvisited.forEach(n => {
                for (let rawK in n.dropoffs) {
                    let k = rawK.toLowerCase();
                    remainingDemand[k] = (remainingDemand[k] || 0) + n.dropoffs[rawK].amount;
                }
            });

            for (let k in remainingDemand) {
                if (allowedSupplies.includes(k)) {
                    let demand = remainingDemand[k];
                    let have = shipCargo[k] || 0;
                    if (demand > have) {
                        unmetHubDemand[k] = demand - have;
                        totalUnmetHubDemand += (demand - have);
                    }
                }
            }

            let shipFillPercent = (maxC - shipSpace) / maxC;

            // Nearest unvisited demander AP per ship-cargo item. Used to tell
            // "dead for now" cargo (demander far away) from cargo a nearby
            // factory is about to consume — only the former is safe to stash
            // at the TH so the ship doesn't boomerang back to retrieve it.
            let nearestDemanderAP = {};
            for (let item in shipCargo) nearestDemanderAP[item.toLowerCase()] = Infinity;
            for (let n of unvisited) {
                if (!n.dropoffs) continue;
                let ap = simTravelAP(currentLoc, parseCoords(n.location), simSector, simDijCache) + 5;
                for (let rk in n.dropoffs) {
                    if (n.dropoffs[rk].amount <= 0) continue;
                    let k = rk.toLowerCase();
                    if (nearestDemanderAP[k] !== undefined && ap < nearestDemanderAP[k]) nearestDemanderAP[k] = ap;
                }
            }
            let bestFactoryAP = Infinity;
            for (let n of unvisited) {
                let ap = simTravelAP(currentLoc, parseCoords(n.location), simSector, simDijCache) + 5;
                if (ap < bestFactoryAP) bestFactoryAP = ap;
            }

            let unmetEnergy = Math.max(0, (remainingDemand['res_c'] || 0) - (shipCargo['res_c'] || 0));
            let shipHasFW = (shipCargo['res_a'] || 0) > 0 || (shipCargo['res_b'] || 0) > 0;
            // Res_C is never hub-supplied (excluded from allowedSupplies for
            // all hub types) — it is procured exclusively via the cycle block
            // below, which does a full-hull bulk station run.  Small res_c
            // demands that don't fill the hull are simply left unmet rather
            // than wasting hundreds of APs for a handful of credits.
            //
            // The cycle block must NOT fire while the ship is still carrying
            // undelivered res_c.  Otherwise the hub step scales the Res_A/Res_B load
            // to the ship's partial free space, producing a partial res_c buy
            // instead of a full-cargo run.  The ship must first deliver all
            // res_c it has to factories; only then does the cycle fire for the next
            // full hull.
            let shipEnergy = shipCargo['res_c'] || 0;
            // cycle is a full-hull bulk operation: fill hull with Res_A/Res_B → travel
            // to station → sell Res_A/Res_B, buy res_c → deliver.  It must NOT fire
            // when the ship is carrying a lot of non-Res_A/Res_B cargo — doing an
            // 88-AP detour for 84 res_c because the hull is full of metal
            // is a massive waste.  Require that Res_A/Res_B capacity (existing Res_A/Res_B +
            // free space) covers at least 80% of the hull.  The ship delivers
            // its other cargo first, freeing space, then cycle fires with a
            // near-full hull.
            let fwCapacity = (shipCargo['res_a'] || 0) + (shipCargo['res_b'] || 0) + shipSpace;
            let cycleNeeded = unmetEnergy >= maxC && !noStationAvailable && fwCapacity >= maxC * 0.8 && shipEnergy === 0;

            // >> cycle override clearing phase
            // When the cycle conditions are met EXCEPT the hull is too full of
            //  other cargo (fwCapacity < 80%), proactively clear the hull:
            //  deliver existing cargo to the nearest demanding buildings, dump
            //  anything with no building demand at the TH, then let the next
            //  iteration fire the normal cycle block with a near-empty hull.
            if (!cycleNeeded && !noStationAvailable && unmetEnergy >= maxC && shipEnergy === 0 && fwCapacity < maxC * 0.8) {
                let cleared = false;
                // Collect clearable items (everything except res_a, res_b, res_c —
                // Res_A/Res_B contributes to fwCapacity and res_c is already 0).
                let clearableItems = [];
                for (let item in shipCargo) {
                    let k = item.toLowerCase();
                    if (k === 'res_a' || k === 'res_b' || k === 'res_c') continue;
                    if (PROTECTED_CARGO.has(k)) continue;
                    let amt = shipCargo[item] || 0;
                    if (amt <= 0) continue;
                    clearableItems.push({ item: item, k: k, amt: amt });
                }
                // Sort by amount descending — clear biggest chunks first.
                clearableItems.sort((a, b) => b.amt - a.amt);

                let leftoverForTO = {};

                for (let ci of clearableItems) {
                    let remaining = ci.amt;
                    // Find unvisited buildings that demand this item, sorted by
                    // distance from currentLoc.
                    let demanders = [];
                    for (let ui = 0; ui < unvisited.length; ui++) {
                        let n = unvisited[ui];
                        if (!n.dropoffs) continue;
                        for (let rawItem in n.dropoffs) {
                            if (rawItem.toLowerCase() === ci.k && n.dropoffs[rawItem].amount > 0) {
                                let d = simTravelAP(currentLoc, parseCoords(n.location), simSector, simDijCache);
                                demanders.push({ node: n, idx: ui, dist: d, rawItem: rawItem });
                                break;
                            }
                        }
                    }
                    demanders.sort((a, b) => a.dist - b.dist);

                    for (let dm of demanders) {
                        if (remaining <= 0) break;
                        let need = dm.node.dropoffs[dm.rawItem].amount;
                        let give = Math.min(need, remaining);
                        if (give <= 0) continue;

                        let stepRecord = {
                            location: dm.node.location,
                            name: dm.node.name,
                            pickups: {},
                            dropoffs: {},
                            destinationType: "factory"
                        };
                        stepRecord.dropoffs[dm.rawItem] = { amount: give, id: dm.node.dropoffs[dm.rawItem].id };
                        routeSteps.push(stepRecord);

                        shipCargo[ci.item] -= give;
                        let fromMag = Math.min(give, simAuxHoldUsed);
                        simAuxHoldUsed -= fromMag;
                        shipSpace += (give - fromMag);
                        dm.node.dropoffs[dm.rawItem].amount -= give;
                        remaining -= give;
                        currentLoc = parseCoords(dm.node.location);
                        cleared = true;

                        // Remove node from unvisited if fully satisfied.
                        let remainingDrop = Object.values(dm.node.dropoffs).reduce((a, b) => a + b.amount, 0);
                        let remainingPick = Object.values(dm.node.pickups).reduce((a, b) => a + b.amount, 0);
                        if (remainingDrop === 0 && remainingPick === 0) {
                            unvisited.splice(dm.idx, 1);
                            // Adjust indices in demanders list for the splice.
                            for (let dj = 0; dj < demanders.length; dj++) {
                                if (demanders[dj].idx > dm.idx) demanders[dj].idx--;
                            }
                        }
                    }

                    // Anything left over with no building demand → TH.
                    if (remaining > 0) {
                        if (!exportList.includes(ci.k)) {
                            leftoverForTO[ci.item] = (leftoverForTO[ci.item] || 0) + remaining;
                        }
                    }
                }

                // Emit a single TH dump step for all leftover items.
                if (hasTO && Object.keys(leftoverForTO).length > 0 && toSpace > 0) {
                    let stepRecord = {
                        location: toCoordStr,
                        name: "Transit Hub (cycle Clear)",
                        pickups: {},
                        dropoffs: {},
                        destinationType: "to"
                    };
                    for (let item in leftoverForTO) {
                        if (toSpace <= 0) break;
                        let dropAmt = Math.min(leftoverForTO[item], toSpace);
                        if (dropAmt <= 0) continue;
                        shipCargo[item] = (shipCargo[item] || 0) - dropAmt;
                        let fromMag = Math.min(dropAmt, simAuxHoldUsed);
                        simAuxHoldUsed -= fromMag;
                        shipSpace += (dropAmt - fromMag);
                        toSpace -= dropAmt;
                        toInventory[item] = (toInventory[item] || 0) + dropAmt;
                        let displayName = item.charAt(0).toUpperCase() + item.slice(1);
                        stepRecord.dropoffs[displayName] = { amount: dropAmt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
                    }
                    routeSteps.push(stepRecord);
                    currentLoc = toLoc;
                    cleared = true;
                }

                if (cleared) continue;
            }

            let dumpableCargo = {};
            let totalDumpable = 0;
            const STASH_FILL_THRESHOLD = 0.7;
            const STASH_FAR_RATIO = 1.5;
            const STASH_FAR_AP = 45;
            for (let item in shipCargo) {
                let k = item.toLowerCase();
                if (PROTECTED_CARGO.has(k)) continue;
                let have = shipCargo[item] || 0;
                let demand = remainingDemand[k] || 0;
                let excess = have - demand;
                if (excess > 0 && !(cycleNeeded && (k === 'res_a' || k === 'res_b'))) {
                    dumpableCargo[item] = excess;
                    totalDumpable += excess;
                }
                // Stashable (needed-but-deferred) portion: only when the ship is
                // full enough that freeing space matters, and the item's nearest
                // demander is far enough that we won't immediately retrieve it.
                // Hub-supplied consumables (res_a/res_b/res_d) are excluded:
                // they are bought on-demand and stashing-while-demanded would
                // just trigger a hub reload loop (stash -> demand still unmet ->
                // hub buys more -> stash again). Only supply-chain items picked
                // up from buildings (metal, gems, etc.) may be deferred to the TH.
                let isHubSupply = allowedSupplies.includes(k);
                if (shipFillPercent > STASH_FILL_THRESHOLD && demand > 0 && !isHubSupply) {
                    // Don't stash needed-but-deferred cargo while unvisited
                    // factories still PRODUCE this item — stashing frees space
                    // which the ship then uses to pick up MORE of the same item
                    // at the next producer, creating an AM→TO→AM→TH accumulation
                    // loop. Only stash after all producers are visited.
                    let stillProduced = false;
                    for (let n of unvisited) {
                        if (!n.pickups) continue;
                        for (let pk in n.pickups) {
                            if (pk.toLowerCase() === k && n.pickups[pk].amount > 0) { stillProduced = true; break; }
                        }
                        if (stillProduced) break;
                    }
                    if (stillProduced) continue;
                    let nap = nearestDemanderAP[k] !== undefined ? nearestDemanderAP[k] : Infinity;
                    let far = (nap >= STASH_FAR_AP) && (bestFactoryAP === Infinity || nap >= bestFactoryAP * STASH_FAR_RATIO);
                    if (far) {
                        let stashable = Math.min(have, demand);
                        if (stashable > 0) {
                            dumpableCargo[item] = (dumpableCargo[item] || 0) + stashable;
                            totalDumpable += stashable;
                        }
                    }
                }
            }

            // Stashed (non-export) items the remaining factories still demand and
            // the ship doesn't yet carry enough of. Exports are semi-permanent
            // (reserved for the long-haul subsystem) and are never pulled back for
            // ordinary factory delivery. Gated on a low fill so the ship only
            // retrieves when it has room to carry the batch toward a demander.
            // Blocked right after a TH stash visit (when factories remain) to
            // prevent stash→immediate-retrieve ping-pong: the ship must visit a
            // factory first, then return to the TH for retrieval later.
            let prevWasTO = routeSteps.length > 0 && routeSteps[routeSteps.length - 1].destinationType === 'to';
            let allowRetrieval = !prevWasTO || unvisited.length === 0;
            let retrievableCargo = {};
            let totalRetrievable = 0;
            if (hasTO && shipFillPercent < 0.5 && allowRetrieval) {
                for (let item in toInventory) {
                    if (toInventory[item] <= 0) continue;
                    let k = item.toLowerCase();
                    if (exportList.includes(k)) continue;
                    if (PROTECTED_CARGO.has(k)) continue;
                    let need = Math.max(0, (remainingDemand[k] || 0) - (shipCargo[k] || 0));
                    if (need > 0 && shipSpace > 0) {
                        let take = Math.min(toInventory[item], need, shipSpace);
                        if (take > 0) { retrievableCargo[item] = take; totalRetrievable += take; }
                    }
                }
            }

            let toUseful = hasTO && ((toSpace > 0 && totalDumpable > 0) || totalRetrievable > 0);
            if (unvisited.length === 0 && !toUseful) {
                break;
            }

            let currentSupplies = 0;
            allowedSupplies.forEach(s => { currentSupplies += (shipCargo[s] || 0); });

            let bestNodeIndex = -1;
            let bestScore = -Infinity;
            let destinationType = "none";
            let hubLoadPlan = {};
            let bestStationCandidate = null; // { st, eval } for the station res_c run branch
            let hubRate = 0;
            let bestFactoryRate = 0;
            let bestFactoryIdx = -1;

            if (totalUnmetHubDemand > 0 && shipSpace > 0 && !cycleNeeded) {
                let hubDist = simTravelAP(currentLoc, hubLoc, simSector, simDijCache);
                let potentialLoad = Math.min(totalUnmetHubDemand, shipSpace);

                if (potentialLoad >= minTrade) {
                    // Build the load plan: simulate a virtual pass through
                    // factories sorted by distance from the hub, allocating
                    // supplies to each factory's demand after consuming what
                    // the ship already carries.
                    hubLoadPlan = {};
                    let loadTempSpace = shipSpace;
                    let virtualCargo = JSON.parse(JSON.stringify(shipCargo));
                    let sortedClone = JSON.parse(JSON.stringify(unvisited))
                        .sort((a,b) => simTravelAP(hubLoc, parseCoords(a.location), simSector, simDijCache)
                                     - simTravelAP(hubLoc, parseCoords(b.location), simSector, simDijCache));

                    for (let n of sortedClone) {
                        for (let rawK in n.dropoffs) {
                            if (loadTempSpace <= 0) break;
                            let k = rawK.toLowerCase();
                            if (allowedSupplies.includes(k)) {
                                let needed = n.dropoffs[rawK].amount;
                                let consume = Math.min(needed, virtualCargo[k] || 0);
                                virtualCargo[k] = (virtualCargo[k] || 0) - consume;
                                let netNeeded = needed - consume;

                                if (netNeeded > 0) {
                                    let loadAmt = Math.min(netNeeded, loadTempSpace);
                                    if (loadAmt > 0) {
                                        hubLoadPlan[rawK] = (hubLoadPlan[rawK] || 0) + loadAmt;
                                        loadTempSpace -= loadAmt;
                                        n.dropoffs[rawK].amount -= (consume + loadAmt);
                                    }
                                }
                            }
                        }
                    }

                    // Sweep lookahead: simulate a nearest-neighbor walk from
                    // the hub through factories. Only count MARGINAL action —
                    // drops from hub-loaded supplies and the pickups they
                    // enable. Drops from pre-existing ship cargo are NOT
                    // counted (the ship could deliver those without the hub
                    // detour). Pickups at a factory count only if hub cargo was
                    // dropped there; those pickups go into the hub-cargo pool
                    // so chain deliveries (hub res_c → metal pickup → metal
                    // drop at next factory) count as hub-enabled action.
                    let sweepOrigCargo = JSON.parse(JSON.stringify(shipCargo));
                    let sweepHubCargo = {};
                    for (let rk in hubLoadPlan) {
                        let k = rk.toLowerCase();
                        sweepHubCargo[k] = (sweepHubCargo[k] || 0) + hubLoadPlan[rk];
                    }
                    let sweepSpace = shipSpace - Object.values(hubLoadPlan).reduce((a,b)=>a+b, 0);
                    let sweepRemainingDemand = {};
                    for (let n of unvisited) {
                        for (let rk in n.dropoffs) {
                            let k = rk.toLowerCase();
                            sweepRemainingDemand[k] = (sweepRemainingDemand[k] || 0) + n.dropoffs[rk].amount;
                        }
                    }
                    let sweepNodes = unvisited.slice();
                    let sweepLoc = hubLoc;
                    let sweepAP = 0;
                    let sweepAction = 0;
                    let sweepMag = simAuxHoldUsed;

                    while (sweepNodes.length > 0) {
                        let bestIdx = -1, bestDist = Infinity;
                        for (let i = 0; i < sweepNodes.length; i++) {
                            let d = simTravelAP(sweepLoc, parseCoords(sweepNodes[i].location), simSector, simDijCache);
                            if (d < bestDist) { bestDist = d; bestIdx = i; }
                        }
                        if (bestIdx < 0) break;
                        let node = sweepNodes[bestIdx];
                        let nodeAction = 0;
                        let nodeHadHubDrop = false;

                        for (let rk in node.dropoffs) {
                            let k = rk.toLowerCase();
                            let total = (sweepOrigCargo[k] || 0) + (sweepHubCargo[k] || 0);
                            if (total > 0 && node.dropoffs[rk].amount > 0) {
                                let drop = Math.min(node.dropoffs[rk].amount, total);
                                let origDrop = Math.min(drop, sweepOrigCargo[k] || 0);
                                let hubDrop = drop - origDrop;
                                sweepOrigCargo[k] = (sweepOrigCargo[k] || 0) - origDrop;
                                sweepHubCargo[k] = (sweepHubCargo[k] || 0) - hubDrop;
                                sweepRemainingDemand[k] = (sweepRemainingDemand[k] || 0) - drop;
                                let fromMag = Math.min(drop, sweepMag);
                                sweepMag -= fromMag;
                                sweepSpace += (drop - fromMag);
                                if (hubDrop > 0) {
                                    sweepAction += hubDrop;
                                    nodeAction += hubDrop;
                                    nodeHadHubDrop = true;
                                }
                            }
                        }
                        if (nodeHadHubDrop) {
                            for (let rk in node.pickups) {
                                let k = rk.toLowerCase();
                                let avail = node.pickups[rk].amount;
                                let isExport = exportList.includes(k);
                                let sectorStillNeeds = Math.max(0, (sweepRemainingDemand[k] || 0) - (sweepOrigCargo[k] || 0) - (sweepHubCargo[k] || 0));
                                let maxTake = isExport ? avail : sectorStillNeeds;
                                if (maxTake > 0 && sweepSpace > 0) {
                                    let take = Math.min(avail, sweepSpace, maxTake);
                                    sweepHubCargo[k] = (sweepHubCargo[k] || 0) + take;
                                    sweepSpace -= take;
                                    sweepAction += take;
                                    nodeAction += take;
                                }
                            }
                        }
                        sweepNodes.splice(bestIdx, 1);
                        if (nodeAction === 0) continue;
                        sweepAP += bestDist + 5;
                        sweepLoc = parseCoords(node.location);
                    }

                    let totalAP = hubDist + 5 + sweepAP;
                    let hubScore = sweepAction > 0
                        ? Math.pow(sweepAction, 1.5) / Math.pow(totalAP, 1.2)
                        : 0;
                    if (hubDist === 0) hubScore *= 1.5;
                    hubRate = sweepAction > 0 ? sweepAction / totalAP : 0;

                    if (hubScore > bestScore) {
                        bestScore = hubScore;
                        destinationType = "hub";
                    }
                }
            }

            if (hasTO && (totalDumpable > 0 || totalRetrievable > 0)) {
                let toDist = simTravelAP(currentLoc, toLoc, simSector, simDijCache);
                let apCost = toDist + 5;
                let potentialDump = Math.min(totalDumpable, toSpace);
                let potentialAction = potentialDump + totalRetrievable;

                if (potentialAction >= minTrade) {
                    let toScore = Math.pow(potentialAction, 1.5) / Math.pow(apCost, 1.2);

                    if (toDist === 0) toScore *= 10;
                    if (shipFillPercent > 0.75) toScore *= 2.5;
                    if (totalRetrievable > 0 && shipFillPercent < 0.4) toScore *= 2.0;
                    if (unvisited.length === 0) toScore += 100000;

                    if (toScore > bestScore) {
                        bestScore = toScore;
                        destinationType = "to";
                    }
                }
            }

            // -- Station res_c run -----------------------------------------
            // Res_C is never hub-supplied (excluded from allowedSupplies
            // for all hub types) so the hub reload branch will never
            // satisfy res_c demand.  Instead, route the ship to a real
            // tracked station (in the same sector or an adjacent one) to
            // pick up res_c via the standard resupply cycle: buy res_a+res_b at
            // the hub -> travel to the station -> sell Res_A/Res_B + buy res_c ->
            // return.  The station's own price/stock is sourced from the
            // trade-tracker store (must be visited at least once).
            //
            // Cost/appletuning: we cap the candidate search to "best per
            // sector" so the per-iteration cost stays O(sectors_with_sbs)
            // rather than O(all_tracked_stations).  The post-loop
            // optimizeFactoryRuns is what straightens the final order.
            let energyDemand = remainingDemand['res_c'] || 0;
            let haveEnergy = shipCargo['res_c'] || 0;
            if (cycleNeeded) {
                let hubEntry = null;
                try { hubEntry = (typeof findExportToEntry === 'function') ? findExportToEntry(getTrackerStore(), hubLoc) : null; } catch (e) { hubEntry = null; }
                if (hubEntry && hubEntry.commodities) {
                    let resMap = simResNameMap();
                    let resAId   = resMap['res_a']   && resMap['res_a'].id;
                    let resBId  = resMap['res_b']  && resMap['res_b'].id;
                    let resCId = resMap['res_c'] && resMap['res_c'].id;
                    if (resAId && resBId && resCId &&
                        hubEntry.commodities[resAId] && hubEntry.commodities[resBId] && hubEntry.commodities[resCId]) {

                        // One Dijkstra per sector from the ship's current
                        // position covers every same-sector station. Track
                        // the best per-sector candidate, then pick the best
                        // across sectors at the end.
                        let allStations = simGetTrackedStations();
                        if (allStations.length > 0) {
                            // Group stations by sector; for each sector,
                            // evaluate the best one and keep it. This is a
                            // coarse sieve — within a sector the chosen
                            // station may not be the truly optimal one, but
                            // the per-iteration scoring cost stays linear in
                            // the number of sectors with stations (usually
                            // very small).
                            let bySector = {};
                            for (let s of allStations) {
                                if (!bySector[s.sector]) bySector[s.sector] = [];
                                bySector[s.sector].push(s);
                            }

                            let bestStPerSector = {};
                            for (let sec in bySector) {
                                let bestInSec = null;
                                for (let s of bySector[sec]) {
                                    let cycleEval = simEvaluatecycleRun(
                                        s, hubEntry, currentLoc, simSector,
                                        simDijCache, simCrossCache, maxC
                                    );
                                    if (!cycleEval || !cycleEval.feasible) continue;
                                    let metric = cycleEval.resCQty / (cycleEval.oneWayAp + 10);
                                    if (!bestInSec || metric > bestInSec.metric) {
                                        bestInSec = { st: s, eval: cycleEval, metric: metric };
                                    }
                                }
                                if (bestInSec) bestStPerSector[sec] = bestInSec;
                            }

                            // Pick the overall-best station by res_c items
                            // per AP (one-way travel + 2 trade actions).  This
                            // is the same volume-per-AP principle used for
                            // factory and hub candidates: a close station
                            // with lots of stock wins; a far station with
                            // little stock loses to nearby factories.
                            let bestStChoice = null;
                            let bestStMetric = -1;
                            for (let sec in bestStPerSector) {
                                let cand = bestStPerSector[sec];
                                if (!cand) continue;
                                if (cand.metric > bestStMetric) {
                                    bestStMetric = cand.metric;
                                    bestStChoice = cand;
                                }
                            }

                            if (bestStChoice) {
                                let stAction = bestStChoice.eval.resCQty;
                                let stAP = bestStChoice.eval.oneWayAp + 10;
                                let stScore = Math.pow(stAction, 1.5) / Math.pow(stAP, 1.2);
                                if (stScore > bestScore) {
                                    bestStationCandidate = bestStChoice;
                                    bestScore = stScore;
                                    destinationType = "station";
                                }
                            }
                        }
                    }
                }
            }

            if (cycleNeeded && !bestStationCandidate) {
                noStationAvailable = true;
            }

            for (let i = 0; i < unvisited.length; i++) {
                let node = unvisited[i];
                let dist = simTravelAP(currentLoc, parseCoords(node.location), simSector, simDijCache);
                let apCost = dist + 5;

                let simulatedDrop = 0;
                let simulatedPick = 0;
                let tempSpace = shipSpace;
                let tempAuxHold = simAuxHoldUsed;
                let synergyBonus = 1.0;

                for (let rawItem in node.dropoffs) {
                    let item = rawItem.toLowerCase();
                    let req = node.dropoffs[rawItem].amount;
                    if (shipCargo[item] > 0) {
                        let canDrop = Math.min(req, shipCargo[item]);
                        simulatedDrop += canDrop;
                        let fromMag = Math.min(canDrop, tempAuxHold);
                        tempAuxHold -= fromMag;
                        tempSpace += (canDrop - fromMag);
                        if (canDrop > 0 && dumpableCargo[item] > 0) synergyBonus += 0.2;
                    }
                }

                for (let rawItem in node.pickups) {
                    let item = rawItem.toLowerCase();
                    let avail = node.pickups[rawItem].amount;
                    let isExport = exportList.includes(item);
                    let sectorStillNeeds = Math.max(0, (remainingDemand[item] || 0) - (shipCargo[item] || 0) - (toInventory[item] || 0));
                    let maxWeShouldTake = isExport ? avail : sectorStillNeeds;

                    if (maxWeShouldTake > 0 && tempSpace > 0) {
                        let canTake = Math.min(avail, tempSpace, maxWeShouldTake);
                        simulatedPick += canTake;
                        tempSpace -= canTake;
                        if (canTake > 0 && shipCargo[item] > 0) synergyBonus += 0.5;
                    }
                }

                let totalAction = simulatedDrop + simulatedPick;

                if (totalAction >= minTrade) {
                    if (simulatedDrop > 0) {
                        let factoryRate = totalAction / apCost;
                        if (factoryRate > bestFactoryRate) {
                            bestFactoryRate = factoryRate;
                            bestFactoryIdx = i;
                        }
                    }
                    let score = Math.pow(totalAction, 1.5) / Math.pow(apCost, 1.2);
                    score *= synergyBonus;

                    if (simulatedDrop > 0 && simulatedPick > 0) score *= 1.3;

                    if (shipFillPercent > 0.75) {
                        if (simulatedDrop > simulatedPick) score *= 2.0;
                        else score *= 0.4;
                    }
                    if (shipFillPercent < 0.25) {
                        if (simulatedPick > simulatedDrop) score *= 1.5;
                    }

                    if (score > bestScore) {
                        bestScore = score;
                        bestNodeIndex = i;
                        destinationType = "factory";
                    }
                }
            }

            // AP-efficiency guard: if the hub won on exponent score but
            // a factory has a better linear action/AP ratio, prefer the
            // factory. The exponent formula inflates large sweeps;
            // this guard ensures the hub only wins when it's genuinely
            // more AP-efficient than the best individual factory visit.
            if (destinationType === "hub" && bestFactoryRate > hubRate && bestFactoryIdx >= 0) {
                destinationType = "factory";
                bestNodeIndex = bestFactoryIdx;
            }

            if (destinationType === "none") break;

            if (destinationType === "hub") {
                let stepRecord = { location: hubLocStr, name: "Primary Hub (Supply Reload)", pickups: {}, dropoffs: {}, destinationType: "hub" };
                for (let rawItem in hubLoadPlan) {
                    let item = rawItem.toLowerCase();
                    let amt = hubLoadPlan[rawItem];
                    shipCargo[item] = (shipCargo[item] || 0) + amt;
                    shipSpace -= amt;
                    stepRecord.pickups[rawItem] = { amount: amt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
                }
                routeSteps.push(stepRecord);
                currentLoc = hubLoc;
            }
            else if (destinationType === "to") {
                let stepRecord = { location: toCoordStr, name: "Transit Hub (Secondary Hub)", pickups: {}, dropoffs: {}, destinationType: "to" };
                // Drop stashable/excess cargo into the TH.
                for (let item in dumpableCargo) {
                    if (toSpace <= 0) break;
                    let dropAmt = Math.min(dumpableCargo[item], toSpace);
                    if (dropAmt <= 0) continue;

                    shipCargo[item] = (shipCargo[item] || 0) - dropAmt;
                    let fromMag = Math.min(dropAmt, simAuxHoldUsed);
                    simAuxHoldUsed -= fromMag;
                    shipSpace += (dropAmt - fromMag);
                    toSpace -= dropAmt;
                    toInventory[item] = (toInventory[item] || 0) + dropAmt;
                    let displayName = item.charAt(0).toUpperCase() + item.slice(1);
                    stepRecord.dropoffs[displayName] = { amount: dropAmt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
                }
                // Retrieve stashed (non-export) cargo the remaining factories need.
                for (let item in retrievableCargo) {
                    if (shipSpace <= 0) break;
                    let takeAmt = Math.min(retrievableCargo[item], shipSpace);
                    if (takeAmt <= 0) continue;
                    toInventory[item] = (toInventory[item] || 0) - takeAmt;
                    if (toInventory[item] <= 0) delete toInventory[item];
                    shipCargo[item] = (shipCargo[item] || 0) + takeAmt;
                    shipSpace -= takeAmt;
                    toSpace += takeAmt;
                    let displayName = item.charAt(0).toUpperCase() + item.slice(1);
                    stepRecord.pickups[displayName] = { amount: takeAmt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
                }
                routeSteps.push(stepRecord);
                currentLoc = toLoc;
            }
            else if (destinationType === "station") {
                // cycle-style res_c run: hub stop (buy Res_A/Res_B) + station stop
                // (sell Res_A/Res_B, buy res_c) chained together.  We emit two
                // consecutive steps: a "hub detour" load of Res_A/Res_B and the
                // station trade.  The optimizer at the end of the function
                // will straighten their order/location as needed.
                let evalRes = bestStationCandidate.eval;
                let stationInfo = bestStationCandidate.st;
                // -- Step 1: load Res_A/Res_B at the hub in the 123:84 ratio to fill
                // ALL available space.  We do NOT clamp by evalRes.resAQty /
                // resBQty (tracker-projected station buy capacity) — those
                // are conservative estimates for scoring only.  Loading the
                // full hull ensures the trip is worthwhile even if tracker
                // data is stale.  The runtime trade screen handles actual
                // stock limits.
                const FW_FOOD = 123, FW_WATER = 84, FW_SUM = FW_FOOD + FW_WATER;
                let totalFWCap = (shipCargo['res_a'] || 0) + (shipCargo['res_b'] || 0) + shipSpace;
                let desiredResA = Math.floor(totalFWCap * FW_FOOD / FW_SUM);
                let desiredResB = totalFWCap - desiredResA;
                let foodLoad = Math.max(0, desiredResA - (shipCargo['res_a'] || 0));
                let waterLoad = Math.max(0, desiredResB - (shipCargo['res_b'] || 0));
                if (foodLoad + waterLoad > shipSpace) {
                    let total = foodLoad + waterLoad;
                    if (total > 0 && shipSpace > 0) {
                        foodLoad = Math.floor(foodLoad * shipSpace / total);
                        waterLoad = shipSpace - foodLoad;
                    } else {
                        foodLoad = 0; waterLoad = 0;
                    }
                }
                if (foodLoad > 0 || waterLoad > 0) {
                    let hubLoad = {};
                    if (foodLoad > 0)  hubLoad['res_a']  = foodLoad;
                    if (waterLoad > 0) hubLoad['res_b'] = waterLoad;
                    let hubStep = {
                        location: hubLocStr,
                        name: "Primary Hub (Res_A/Res_B for Station)",
                        pickups: {},
                        dropoffs: {},
                        destinationType: "hub"
                    };
                    for (let rawItem in hubLoad) {
                        let item = rawItem.toLowerCase();
                        let amt = hubLoad[rawItem];
                        shipCargo[item] = (shipCargo[item] || 0) + amt;
                        shipSpace -= amt;
                        hubStep.pickups[rawItem] = { amount: amt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
                    }
                    routeSteps.push(hubStep);
                }
                // -- Step 2: station trade.  Sell Res_A/Res_B (dropoffs) and buy
                // res_c (pickups) in a single combined step.  Per the game
                // dual-trade handling (the script's split-transfer bypass),
                // a single trade screen allows simultaneous buy+sell.  If
                // the server rejects the combined trade, the QOL step
                // advancer will fall back to split dropoffs then pickups.
                //
                // The cycle block is immutable: sell ALL res_a+res_b the ship
                // carries and fill the ENTIRE hull with res_c.  We do NOT
                // clamp by evalRes.resAQty/resBQty/resCQty — those are
                // profitability-evaluation quantities based on (possibly
                // stale) tracker stock data.  The actual trade screen /
                // reality checker handles real stock limits at runtime.
                let resASell = shipCargo['res_a'] || 0;
                let resBSell = shipCargo['res_b'] || 0;
                // Calculate regular space that will be freed by selling Res_A/Res_B,
                // accounting for aux_hold items (they drain aux_hold, not
                // regular space).
                let foodFromMag = Math.min(resASell, simAuxHoldUsed);
                let waterFromMag = Math.min(resBSell, simAuxHoldUsed - foodFromMag);
                let freedRegular = (resASell - foodFromMag) + (resBSell - waterFromMag);
                let resCBuy = shipSpace + freedRegular;
                let stStep = {
                    location: '[' + evalRes.stationCoords.x + ',' + evalRes.stationCoords.y + ']',
                    name: stationInfo.entry.name || 'Station (Res_C Run)',
                    pickups: {},
                    dropoffs: {},
                    destinationType: "station"
                };
                if (resASell > 0) {
                    shipCargo['res_a'] = (shipCargo['res_a'] || 0) - resASell;
                    simAuxHoldUsed -= foodFromMag;
                    shipSpace += (resASell - foodFromMag);
                    stStep.dropoffs['res_a'] = { amount: resASell, id: (simResNameMap()['res_a'] && simResNameMap()['res_a'].id) || 'res_a' };
                }
                if (resBSell > 0) {
                    shipCargo['res_b'] = (shipCargo['res_b'] || 0) - resBSell;
                    simAuxHoldUsed -= waterFromMag;
                    shipSpace += (resBSell - waterFromMag);
                    stStep.dropoffs['res_b'] = { amount: resBSell, id: (simResNameMap()['res_b'] && simResNameMap()['res_b'].id) || 'res_b' };
                }
                if (resCBuy > 0) {
                    shipCargo['res_c'] = (shipCargo['res_c'] || 0) + resCBuy;
                    shipSpace -= resCBuy;
                    stStep.pickups['res_c'] = { amount: resCBuy, id: (simResNameMap()['res_c'] && simResNameMap()['res_c'].id) || 'res_c' };
                }
                routeSteps.push(stStep);
                // Update bookkeeping: the ship is now AT the station
                // (sector + coords) and the next iteration will treat
                // currentLoc accordingly.  This routes subsequent
                // factory/TH visits through the station as a waypoint,
                // which the post-loop optimizer can smooth.
                currentLoc = { x: evalRes.stationCoords.x, y: evalRes.stationCoords.y };
                // Sector we are now in (for simTravelAP on the next iter).
                simSector = stationInfo.sector;
                // Virtually pre-deliver the res_c we just bought to the
                // unvisited res_c-demanding structures so the next loop
                // iteration sees a reduced demand and doesn't re-fire the
                // cycle branch.  We do this in currentLoc-proximity order
                // (closest building first), like a normal route — and
                // the post-loop optimizeFactoryRuns will smooth the final
                // order.
                if (resCBuy > 0) {
                    // Emit one factory dropoff step per unvisited building
                    // whose remaining Res_C demand can be (partially or
                    // fully) covered by the res_c we just bought.  The
                    // step is a real, navigable "fly here and trade"
                    // entry on the route — not a virtual reduction.
                    // Distance from currentLoc (the station) sorts the
                    // deliveries; the post-loop optimizer can smooth the
                    // final order.
                    let remaining = resCBuy;
                    let cand = [];
                    for (let ui = 0; ui < unvisited.length; ui++) {
                        const n = unvisited[ui];
                        if (!n.dropoffs || !n.dropoffs['res_c']) continue;
                        if (n.dropoffs['res_c'].amount <= 0) continue;
                        const d = simTravelAP(currentLoc, parseCoords(n.location), simSector, simDijCache);
                        cand.push({ node: n, idx: ui, dist: d, loc: parseCoords(n.location) });
                    }
                    cand.sort((a, b) => a.dist - b.dist);
                    // We track which unvisited indices to remove after
                    // applying all reductions (filtering in one pass at the
                    // end is safer than splicing in-place).
                    let toRemove = new Set();
                    for (const c of cand) {
                        if (remaining <= 0) break;
                        const need = c.node.dropoffs['res_c'].amount;
                        if (need <= 0) continue;
                        const give = Math.min(need, remaining);
                        // Emit a factory step: dropoff `give` Res_C at this node.
                        // Other dropoffs at this node (if any) are filled
                        // when the engine re-evaluates and re-visits the
                        // node — but for our test case the only dropoff is
                        // Res_C.  Pickups are unchanged.
                        const stepRecord = {
                            location: c.node.location,
                            name: c.node.name,
                            pickups: {},
                            dropoffs: {},
                            destinationType: "factory"
                        };
                        stepRecord.dropoffs['res_c'] = { amount: give, id: c.node.dropoffs['res_c'].id };
                        routeSteps.push(stepRecord);
                        c.node.dropoffs['res_c'].amount -= give;
                        remaining -= give;
                        shipCargo['res_c'] = (shipCargo['res_c'] || 0) - give;
                        let fromMag = Math.min(give, simAuxHoldUsed);
                        simAuxHoldUsed -= fromMag;
                        shipSpace += (give - fromMag);
                        // If the node is now fully satisfied, mark for removal.
                        const remainingDrop = Object.values(c.node.dropoffs).reduce((a, b) => a + b.amount, 0);
                        const remainingPick = Object.values(c.node.pickups).reduce((a, b) => a + b.amount, 0);
                        if (remainingDrop === 0 && remainingPick === 0) {
                            toRemove.add(c.idx);
                        }
                    }
                    if (toRemove.size > 0) {
                        unvisited = unvisited.filter((_, i) => !toRemove.has(i));
                    }
                }
            }
            else if (destinationType === "factory") {
                let chosen = unvisited[bestNodeIndex];
                let stepRecord = { location: chosen.location, name: chosen.name, pickups: {}, dropoffs: {}, destinationType: "factory" };

                for (let rawItem in chosen.dropoffs) {
                    let item = rawItem.toLowerCase();
                    if (shipCargo[item] > 0) {
                        let req = chosen.dropoffs[rawItem].amount;
                        let dropAmt = Math.min(req, shipCargo[item]);
                        shipCargo[item] -= dropAmt;
                        let fromMag = Math.min(dropAmt, simAuxHoldUsed);
                        simAuxHoldUsed -= fromMag;
                        shipSpace += (dropAmt - fromMag);
                        stepRecord.dropoffs[rawItem] = { amount: dropAmt, id: chosen.dropoffs[rawItem].id };
                        chosen.dropoffs[rawItem].amount -= dropAmt;
                    }
                }

                for (let rawItem in chosen.pickups) {
                    let item = rawItem.toLowerCase();
                    let avail = chosen.pickups[rawItem].amount;
                    let isExport = exportList.includes(item);
                    let sectorStillNeeds = Math.max(0, (remainingDemand[item] || 0) - (shipCargo[item] || 0) - (toInventory[item] || 0));
                    let maxWeShouldTake = isExport ? avail : sectorStillNeeds;

                    if (maxWeShouldTake > 0 && shipSpace > 0) {
                        let takeAmt = Math.min(avail, shipSpace, maxWeShouldTake);
                        shipCargo[item] = (shipCargo[item] || 0) + takeAmt;
                        shipSpace -= takeAmt;
                        stepRecord.pickups[rawItem] = { amount: takeAmt, id: chosen.pickups[rawItem].id };
                        chosen.pickups[rawItem].amount -= takeAmt;
                    }
                }

                routeSteps.push(stepRecord);
                currentLoc = parseCoords(chosen.location);

                let remainingDrop = Object.values(chosen.dropoffs).reduce((a, b) => a + b.amount, 0);
                let remainingPick = Object.values(chosen.pickups).reduce((a, b) => a + b.amount, 0);
                if (remainingDrop === 0 && remainingPick === 0) {
                    unvisited.splice(bestNodeIndex, 1);
                }
            }
        }

        { const __t = __heavyT0('optimizeFactoryRuns#1'); routeSteps = optimizeFactoryRuns(routeSteps, initialShipCargo, initialShipSpace, initialSimAuxHoldUsed, simSector, startLoc); __heavyT1('optimizeFactoryRuns#1', __t); }

        return { steps: routeSteps, toInventory: toInventory };
    }

    // >> Take-All gather route
    function calculateTakeAllRoute(rawNodes, currentLocStr, maxCargo, toCoordStr, toCapacity, takeAllItemsStr, liveCargoStr) {
        let routeSteps = [];
        let toInventory = {};

        let shipCargo = parseLiveCargo(liveCargoStr);
        const PROTECTED_CARGO = new Set(['res_fuel', 'phantom protection']);
        let autoShipSpace = parseInt(GM_getValue('logistics_ship_space', '0'), 10);
        let maxC = (autoShipSpace > 0 ? autoShipSpace : (parseInt(maxCargo, 10) || 200));
        let auxHoldUsed = parseInt(GM_getValue('logistics_mag_scoop_used', '0'), 10) || 0;
        let shipSpace = maxC;
        for (let amt of Object.values(shipCargo)) {
            shipSpace -= amt;
        }
        shipSpace += auxHoldUsed;
        shipSpace = Math.max(0, shipSpace);

        let simAuxHoldUsed = auxHoldUsed;

        let toSpace = parseInt(toCapacity, 10) || 0;

        let simSector = simResolveSector();
        let simDijCache = {};

        let hasTO = toCoordStr && toCoordStr.match(/\[\d+,\d+\]/) && toSpace > 0;
        let toLoc = hasTO ? parseCoords(toCoordStr) : null;
        let currentLoc = parseCoords(currentLocStr || "[7,16]");
        let startLoc = currentLoc;

        let initialShipCargo = JSON.parse(JSON.stringify(shipCargo));
        let initialShipSpace = shipSpace;
        let initialSimAuxHoldUsed = simAuxHoldUsed;

        if (!hasTO) throw new Error('calculateTakeAllRoute: no Transit Hub configured (set TH Coords + TH Space). Take-All requires a TH to dump gathered cargo.');
        let targetSet = new Set((takeAllItemsStr || '').split(',').map(s => s.trim().toLowerCase()).filter(s => s.length > 0));
        if (targetSet.size === 0) throw new Error('calculateTakeAllRoute: no items specified in the take-all list.');

        let nameToIdMap = {};
        rawNodes.forEach(n => {
            Object.entries(n.pickups).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
            Object.entries(n.dropoffs).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
        });

        let unvisited = [];
        for (let n of rawNodes) {
            let clonedPickups = {};
            for (let rawItem in n.pickups) {
                let lc = rawItem.toLowerCase();
                if (targetSet.has(lc) && n.pickups[rawItem].amount > 0) {
                    clonedPickups[rawItem] = { amount: n.pickups[rawItem].amount, id: n.pickups[rawItem].id };
                }
            }
            if (Object.keys(clonedPickups).length > 0) {
                unvisited.push({ location: n.location, name: n.name, pickups: clonedPickups, dropoffs: {} });
            }
        }

        if (unvisited.length === 0) {
            return { steps: [], toInventory: {}, mode: 'take_all' };
        }

        function totalRemaining() {
            let total = 0;
            for (let n of unvisited) {
                for (let rawItem in n.pickups) {
                    total += n.pickups[rawItem].amount;
                }
            }
            return total;
        }

        function tryDumpToTO() {
            let dumpable = {};
            for (let item in shipCargo) {
                if (PROTECTED_CARGO.has(item)) continue;
                if (shipCargo[item] > 0) dumpable[item] = shipCargo[item];
            }
            let totalDumpable = 0;
            for (let item in dumpable) totalDumpable += dumpable[item];
            if (totalDumpable === 0 || toSpace <= 0) return false;

            let stepRecord = { location: toCoordStr, name: "Transit Hub (Take-All Dump)", pickups: {}, dropoffs: {}, destinationType: "to" };
            for (let item in dumpable) {
                if (toSpace <= 0) break;
                let dropAmt = Math.min(dumpable[item], toSpace);
                if (dropAmt <= 0) continue;
                shipCargo[item] = (shipCargo[item] || 0) - dropAmt;
                let fromMag = Math.min(dropAmt, simAuxHoldUsed);
                simAuxHoldUsed -= fromMag;
                shipSpace += (dropAmt - fromMag);
                toSpace -= dropAmt;
                toInventory[item] = (toInventory[item] || 0) + dropAmt;
                let displayName = item.charAt(0).toUpperCase() + item.slice(1);
                stepRecord.dropoffs[displayName] = { amount: dropAmt, id: nameToIdMap[item] || item.replace(/\s/g, '_') };
            }
            routeSteps.push(stepRecord);
            currentLoc = toLoc;
            return true;
        }

        while (true) {
            if (totalRemaining() === 0) break;

            let bestIdx = -1, bestScore = -1, bestNodePickup = 0;
            for (let i = 0; i < unvisited.length; i++) {
                let n = unvisited[i];
                let nodeTargetPickup = 0;
                for (let rawItem in n.pickups) {
                    nodeTargetPickup += n.pickups[rawItem].amount;
                }
                let canTake = Math.min(nodeTargetPickup, shipSpace);
                if (canTake <= 0) continue;
                let dist = simTravelAP(currentLoc, parseCoords(n.location), simSector, simDijCache);
                let apCost = dist + 5;
                let score = Math.pow(canTake, 1.5) / Math.pow(apCost, 1.2);
                if (score > bestScore) {
                    bestScore = score;
                    bestIdx = i;
                    bestNodePickup = nodeTargetPickup;
                }
            }

            if (bestIdx < 0) {
                if (!tryDumpToTO()) break;
                continue;
            }

            if (bestNodePickup > shipSpace) {
                if (tryDumpToTO()) continue;
            }

            let chosen = unvisited[bestIdx];
            let stepRecord = { location: chosen.location, name: chosen.name, pickups: {}, dropoffs: {}, destinationType: "factory" };
            for (let rawItem in chosen.pickups) {
                let avail = chosen.pickups[rawItem].amount;
                if (avail <= 0) continue;
                let takeAmt = Math.min(avail, shipSpace);
                if (takeAmt <= 0) continue;
                let item = rawItem.toLowerCase();
                shipCargo[item] = (shipCargo[item] || 0) + takeAmt;
                shipSpace -= takeAmt;
                stepRecord.pickups[rawItem] = { amount: takeAmt, id: chosen.pickups[rawItem].id };
                chosen.pickups[rawItem].amount -= takeAmt;
            }
            routeSteps.push(stepRecord);
            currentLoc = parseCoords(chosen.location);

            let remainingPick = 0;
            for (let rawItem in chosen.pickups) remainingPick += chosen.pickups[rawItem].amount;
            if (remainingPick === 0) {
                unvisited.splice(bestIdx, 1);
            }
        }

        tryDumpToTO();

        { const __t = __heavyT0('optimizeFactoryRuns#2'); routeSteps = optimizeFactoryRuns(routeSteps, initialShipCargo, initialShipSpace, initialSimAuxHoldUsed, simSector, startLoc); __heavyT1('optimizeFactoryRuns#2', __t); }

        return { steps: routeSteps, toInventory: toInventory, mode: 'take_all' };
    }

    // >> Dump-All sell-off route
    function calculateDumpAllRoute(rawNodes, currentLocStr, maxCargo, liveCargoStr) {
        let routeSteps = [];
        let toInventory = {};

        let shipCargo = parseLiveCargo(liveCargoStr);
        const PROTECTED_CARGO = new Set(['res_fuel', 'phantom protection']);
        let autoShipSpace = parseInt(GM_getValue('logistics_ship_space', '0'), 10);
        let maxC = (autoShipSpace > 0 ? autoShipSpace : (parseInt(maxCargo, 10) || 200));
        let auxHoldUsed = parseInt(GM_getValue('logistics_mag_scoop_used', '0'), 10) || 0;
        let shipSpace = maxC;
        for (let amt of Object.values(shipCargo)) {
            shipSpace -= amt;
        }
        shipSpace += auxHoldUsed;
        shipSpace = Math.max(0, shipSpace);

        let simSector = simResolveSector();
        let simDijCache = {};

        let currentLoc = parseCoords(currentLocStr || "[7,16]");
        let startLoc = currentLoc;

        let initialShipCargo = JSON.parse(JSON.stringify(shipCargo));
        let initialShipSpace = shipSpace;
        let initialSimAuxHoldUsed = auxHoldUsed;

        let dumpable = {};
        let totalDumpable = 0;
        for (let item in shipCargo) {
            if (PROTECTED_CARGO.has(item)) continue;
            if (shipCargo[item] > 0) {
                dumpable[item] = shipCargo[item];
                totalDumpable += shipCargo[item];
            }
        }
        if (totalDumpable === 0) {
            return { steps: [], toInventory: {}, mode: 'dump_all' };
        }

        let coordMap = buildCoordEntryMap().map;
        let nameToIdMap = {};
        rawNodes.forEach(n => {
            Object.entries(n.pickups).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
            Object.entries(n.dropoffs).forEach(([name, data]) => nameToIdMap[name.toLowerCase()] = data.id);
        });

        let candidatesByItem = {};
        let anyCandidate = false;
        for (let item in dumpable) {
            let list = [];
            for (let n of rawNodes) {
                let dropKey = Object.keys(n.dropoffs).find(k => k.toLowerCase() === item);
                if (!dropKey) continue;
                let demand = n.dropoffs[dropKey].amount;
                if (demand <= 0) continue;
                let nLoc = parseCoords(n.location);
                let entry = coordMap[nLoc.x + ',' + nLoc.y];
                if (!entry) continue;
                let resId = resolveResId(entry, n.dropoffs[dropKey].id, dropKey);
                if (!resId) continue;
                let comm = entry.commodities[resId];
                if (!comm || comm.sellToObjPrice <= 0) continue;
                list.push({ node: n, demand: demand, price: comm.sellToObjPrice, resId: resId, dropKey: dropKey });
                anyCandidate = true;
            }
            list.sort((a, b) => (b.price - a.price) || (b.demand - a.demand));
            candidatesByItem[item] = list;
        }

        if (!anyCandidate) {
            throw new Error('calculateDumpAllRoute: no priced buyers found for any cargo item. Open each building\'s trade screen first so the trade tracker has buy prices.');
        }

        let remaining = {};
        for (let item in dumpable) remaining[item] = dumpable[item];

        function totalRemaining() {
            let total = 0;
            for (let item in remaining) total += remaining[item];
            return total;
        }

        while (totalRemaining() > 0) {
            let best = null;
            for (let item in remaining) {
                if (remaining[item] <= 0) continue;
                let list = candidatesByItem[item];
                let cand = list.find(c => c.demand > 0);
                if (!cand) continue;
                let sellQty = Math.min(remaining[item], cand.demand);
                let nLoc = parseCoords(cand.node.location);
                let dist = simTravelAP(currentLoc, nLoc, simSector, simDijCache);
                let apCost = dist + 5;
                let revenue = sellQty * cand.price;
                let score = revenue / Math.pow(apCost, 1.2);
                if (!best || score > best.score) {
                    best = { item: item, cand: cand, sellQty: sellQty, nLoc: nLoc, score: score };
                }
            }

            if (!best) break;

            let displayName = best.item.charAt(0).toUpperCase() + best.item.slice(1);
            let stepRecord = {
                location: best.cand.node.location,
                name: best.cand.node.name,
                pickups: {},
                dropoffs: {},
                destinationType: "factory"
            };
            stepRecord.dropoffs[displayName] = {
                amount: best.sellQty,
                id: nameToIdMap[best.item] || best.item.replace(/\s/g, '_')
            };
            routeSteps.push(stepRecord);
            remaining[best.item] -= best.sellQty;
            best.cand.demand -= best.sellQty;
            currentLoc = best.nLoc;
        }

        { const __t = __heavyT0('optimizeFactoryRuns#3'); routeSteps = optimizeFactoryRuns(routeSteps, initialShipCargo, initialShipSpace, initialSimAuxHoldUsed, simSector, startLoc); __heavyT1('optimizeFactoryRuns#3', __t); }

        return { steps: routeSteps, toInventory: toInventory, mode: 'dump_all' };
    }

    function recalculateRouteOnTheFly(sectorState) {
        __setOp('recalculateRouteOnTheFly');
        let activeData = GM_getValue('logistics_route_v5', { steps: [], history: [] });
        let currentLoc = activeData.history.length > 0 ? activeData.history[activeData.history.length - 1].location : GM_getValue('config_hub_coords', '[7,16]');
        try { currentLoc = document.getElementById('coords').innerText; } catch(e){}

        let cap = GM_getValue('config_max_cargo', '200');
        let toCoord = GM_getValue('config_to_coords', '');
        let toCap = GM_getValue('config_to_cap', '');
        let liveCargoStr = GM_getValue('logistics_live_cargo', '');

        let optimizedData;
        if (activeData.mode === 'take_all') {
            let takeAllItems = GM_getValue('config_take_all_items', '');
            optimizedData = calculateTakeAllRoute(sectorState, currentLoc, cap, toCoord, toCap, takeAllItems, liveCargoStr);
        } else if (activeData.mode === 'dump_all') {
            optimizedData = calculateDumpAllRoute(sectorState, currentLoc, cap, liveCargoStr);
        } else {
            let hubLoc = GM_getValue('config_hub_coords', '[7,16]');
            let hubType = GM_getValue('config_hub_type', 'station');
            let minTrade = GM_getValue('config_min_trade', '25');
            let exports = GM_getValue('config_export_items', '');
            optimizedData = calculateOptimalRoute(sectorState, currentLoc, hubLoc, cap, toCoord, toCap, hubType, minTrade, exports, liveCargoStr);
        }
        optimizedData.history = activeData.history;
        GM_setValue('logistics_route_v5', optimizedData);
        return optimizedData;
    }

    // --- 20. Main Execution Flow & Order of Operations ---
    // This part is intentionally LAST in the concatenation: it is the only
    // load-time dispatcher, so placing it after every declaration guarantees
    // all top-level consts/lets are initialized (no TDZ hazards) by the time
    // it runs. Everything above is hoisted function declarations + literals.
    const currentPath = window.location.pathname;

    __perfMark('page_arrival');
    // Firefox Xray wrappers prevent direct unsafeWindow.X = fn from being
    // visible in the page console, and Tampermonkey (unlike Greasemonkey)
    // does not expose exportFunction as a sandbox global. Use a script-tag
    // event bridge: inject a page-context <script> that defines stub
    // functions dispatching CustomEvents on document (which crosses the
    // Xray boundary); the sandbox listens and calls the real functions.
    // Also register GM_registerMenuCommand entries as a reliable
    // cross-browser fallback. (ADR 023)
    document.addEventListener('logistics-perf-enabled', function(e) { __perfEnabled(e.detail); });
    document.addEventListener('logistics-perf-report', function() { __perfReport(); });
    document.addEventListener('logistics-perf-last', function() { __perfLastReport(); });
    document.addEventListener('logistics-perf-dump', function() { __perfDump(); });
    document.addEventListener('logistics-stop-auto', function() { stopAutoStep(); });
    const __bridge = document.createElement('script');
    __bridge.textContent = [
        "(function(){",
        "window.__perfEnabled=function(on){document.dispatchEvent(new CustomEvent('logistics-perf-enabled',{detail:!!on}));};",
        "window.__perfReport=function(){document.dispatchEvent(new CustomEvent('logistics-perf-report'));};",
        "window.__perfLastReport=function(){document.dispatchEvent(new CustomEvent('logistics-perf-last'));};",
        "window.__perfDump=function(){document.dispatchEvent(new CustomEvent('logistics-perf-dump'));};",
        "window.__stopAuto=function(){document.dispatchEvent(new CustomEvent('logistics-stop-auto'));};",
        "})();"
    ].join('');
    (document.head || document.documentElement).appendChild(__bridge);
    __bridge.remove();
    if (typeof GM_registerMenuCommand === 'function') {
        GM_registerMenuCommand('Enable perf instrumentation', function() { __perfEnabled(true); });
        GM_registerMenuCommand('Disable perf instrumentation', function() { __perfEnabled(false); });
        GM_registerMenuCommand('Dump perf report', function() { __perfDump(); });
        GM_registerMenuCommand('Show last perf report', function() { __perfLastReport(); });
        GM_registerMenuCommand('Stop auto-step', function() { stopAutoStep(); });
    }
    __startWatchdog();
    if (GM_getValue('logistics_perf_enabled', false)) {
        try { __perfCrashRecovery(); }
        catch (e) { /* indexedDB not available */ }
    }

    if (currentPath === '//app/main') {
        syncCargoFromNav();
        // Scrape live terrain from #navarea BEFORE the deferred UI injection
        // (below) calls hpaGetTable() — so the terrain store is up to date
        // before any panel reads it. try/catch: a scrape failure must never
        // break the rest of the script. See ADR 009.
        try { scrapeAndStoreTerrain(); }
        catch (e) { console.error('[terrain] scrape failed:', e); }
        // Deferred terrain version bump: if new terrain was discovered, delay
        // the version increment so active navigation doesn't trigger a per-step
        // macro graph recompile. The dirty flag persists across page loads;
        // only when the user is idle (15s) does the version bump fire → one
        // recompile. See ADR 011.
        if (GM_getValue('logistics_terrain_dirty', false)) {
            setTimeout(() => {
                if (GM_getValue('logistics_terrain_dirty', false)) {
                    GM_setValue('logistics_terrain_dirty', false);
                    const v = GM_getValue('logistics_terrain_version', 0) + 1;
                    GM_setValue('logistics_terrain_version', v);
                    console.log('[terrain] deferred version bump → ' + v + ' (user idle 15s)');
                }
            }, 15000);
        }
    } else if (currentPath === '//app/overview') {
        initBookkeeperParser();
    }
    if (GM_getValue('logistics_needs_recalc', false)) {
        // Deferred off the critical path so the nav screen paints before
        // the sim runs. FIFO ordering of equal-delay setTimeouts guarantees
        // this (queued here, before the panels block below) completes and
        // writes logistics_route_v5 before injectNavHUD/injectDraggableUI
        // read it.
        setTimeout(() => {
            let sectorState = GM_getValue('raw_bookkeeper_data', []);
            try {
                recalculateRouteOnTheFly(sectorState);
                GM_deleteValue('logistics_needs_recalc');
            } catch (e) {
                // Hard-fail policy: keep the recalc flag set so it retries
                // on the next page where userloc + static map are available.
                console.error('[logistics-sim] route recalc failed (flag kept for retry):', e);
            }
        }, 0);
    }

    if (currentPath === '//app/main') {
        // Defer heavy UI injection so the browser can paint the nav screen
        // first. injectNavHUD runs first inside this block so it reads the
        // freshly-recalculated logistics_route_v5 (the deferred recalc above
        // is queued earlier than this setTimeout, so FIFO guarantees it
        // completes first). injectDraggableUI triggers hpaGetTable() (L1
        // top-cache hit after first load), then the exports calc (1
        // Dijkstra), fly-here (~250 options), and tracker.
        setTimeout(() => {
            const __tInj = performance.now();
            const autoActive = GM_getValue('logistics_auto_step', false);
            try { injectDraggableUI(); }
            catch (e) { console.error('[logistics-ui] draggable inject failed:', e); }
            if (!autoActive) {
                try { injectNavHUD(); }
                catch (e) { console.error('[logistics-nav] HUD inject failed:', e); }
                try { injectFlyHerePanel(); }
                catch (e) { console.error('[logistics-flyhere] panel inject failed:', e); }
                try { injectExportsCalculator(); }
                catch (e) { console.error('[logistics-exports] panel inject failed:', e); }
                try { injectTrackerPanel(); }
                catch (e) { console.error('[logistics-tracker] panel inject failed:', e); }
            }
            if (GM_getValue('logistics_perf_enabled', false)) console.log('[perf] nav_inject: ' + (performance.now() - __tInj).toFixed(1) + 'ms');
        }, 0);
        try { resumeFlightAfterAmbush(); }
        catch (e) { console.error('[logistics-ambush] resume failed:', e); }
    } else if (currentPath === '//app/overview') {
        injectBuildingsUI();
    } else if (currentPath.includes('/app/trade') || currentPath.includes('/app/manage')) {
        const __tHUD = performance.now();
        injectTradeHUD();
        if (GM_getValue('logistics_perf_enabled', false)) console.log('[perf] injectTradeHUD: ' + (performance.now() - __tHUD).toFixed(1) + 'ms');
        if (currentPath.includes('/app/manage')) {
            try { capturePersonalToStock(); }
            catch (e) { console.error('[logistics-exports] TH stock capture failed:', e); }
        }
        if (currentPath.includes('/app/trade') ||
            currentPath.includes('/app/trade2') ||
            currentPath.includes('/app/trade3')) {
            try {
                const tracked = captureTradeScreen('load');
                console.log('[logistics-tracker] captureTradeScreen on', currentPath,
                    '->', tracked ? (tracked.type + ' loc ' + tracked.userloc + ' (' + Object.keys(tracked.commodities).length + ' res)') : 'null');
                if (tracked) injectTrackerBadge(tracked);
                window.addEventListener('logisticsTradeSubmitted', () => {
                    try { captureTradeScreen('pre-transfer'); } catch(e){ console.error('[logistics-tracker] pre-transfer capture failed:', e); }
                });
            } catch (e) {
                console.error('[logistics-tracker] capture/badge failed:', e);
            }
        }
    } else if (currentPath.includes('/app/combat')) {
        if (GM_getValue('config_auto_retreat', true) && GM_getValue('logistics_ambush_resume', null)) {
            const overlay = document.createElement('div');
            overlay.style.cssText = 'position:fixed; top:0; left:0; width:100%; background:#550000; color:#fff; text-align:center; padding:6px; z-index:999999; font-weight:bold; font-size:13px; border-bottom:2px solid #ff0000;';
            overlay.innerText = '\u26a0 Ambush during auto-fly \u2014 auto-retreating...';
            document.body.appendChild(overlay);
            setTimeout(() => {
                const retreatBtn = document.getElementsByName('retreat')[0];
                if (retreatBtn) retreatBtn.click();
                else { overlay.innerText = '\u26a0 Retreat button not found \u2014 retreat manually.'; setTimeout(() => overlay.remove(), 5000); }
            }, 500);
        }
    }

})();