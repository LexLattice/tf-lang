import { queryHash } from './util.js';
import { filtersToRecord } from './filters.js';
import { buildDb } from '@tf-lang/d1-sqlite';
let memo = null;
let memoErr = null;
export function openDb() {
    if (memo)
        return memo;
    if (memoErr)
        throw memoErr;
    try {
        const db = buildDb();
        const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
        const verRow = res[0]?.values?.[0]?.[0];
        const datasetVersion = typeof verRow === 'string' ? verRow : '';
        const where = [
            'WHERE (?1 IS NULL OR modality = ?1)',
            '(?2 IS NULL OR jurisdiction = ?2)',
            "(?3 IS NULL OR (effective_from <= ?3 AND (?3 <= IFNULL(effective_to, '9999-12-31'))))",
        ].join(' AND ');
        memo = {
            db,
            datasetVersion,
            countStmt: db.prepare(`SELECT COUNT(*) as c FROM claims ${where};`),
            sampleStmt: db.prepare(`SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ${where} ORDER BY id LIMIT 10;`),
            listStmt: db.prepare(`SELECT data FROM claims ${where} ORDER BY id LIMIT ?4 OFFSET ?5;`),
            claimStmt: db.prepare('SELECT data FROM claims WHERE id = ?1;'),
        };
        return memo;
    }
    catch (e) {
        memoErr = e instanceof Error ? e : new Error('db_init_failed');
        throw memoErr;
    }
}
function paramsFromFilters(f) {
    return [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
}
function runAll(stmt, map) {
    const out = [];
    while (stmt.step()) {
        out.push(map(stmt.getAsObject()));
    }
    stmt.reset();
    return out;
}
export function count(db, f) {
    const params = paramsFromFilters(f);
    const stmt = db.countStmt;
    stmt.bind(params);
    stmt.step();
    const obj = stmt.getAsObject();
    const n = typeof obj.c === 'number' ? obj.c : 0;
    stmt.reset();
    const evStmt = db.sampleStmt;
    evStmt.bind(params);
    const samples = runAll(evStmt, r => JSON.parse(String(r.ev)));
    return {
        dataset_version: db.datasetVersion,
        query_hash: queryHash(filtersToRecord(f)),
        filters: f,
        n,
        samples,
    };
}
export function list(db, f) {
    const offset = f.offset ?? 0;
    const limit = f.limit ?? 10;
    const params = paramsFromFilters(f);
    const totalStmt = db.countStmt;
    totalStmt.bind(params);
    totalStmt.step();
    const totalObj = totalStmt.getAsObject();
    const total = typeof totalObj.c === 'number' ? totalObj.c : 0;
    totalStmt.reset();
    const listStmt = db.listStmt;
    listStmt.bind([...params, limit, offset]);
    const items = runAll(listStmt, r => JSON.parse(String(r.data)));
    const responseFilters = { ...f, limit, offset };
    return {
        dataset_version: db.datasetVersion,
        query_hash: queryHash(filtersToRecord(responseFilters)),
        filters: responseFilters,
        total,
        items,
    };
}
export function getClaim(db, id) {
    const stmt = db.claimStmt;
    stmt.bind([id]);
    const rows = runAll(stmt, r => JSON.parse(String(r.data)));
    return rows[0] ?? null;
}
