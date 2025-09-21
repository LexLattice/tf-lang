import { describe, it, before, after } from 'node:test';
import { strict as assert } from 'node:assert';
import { exec } from 'node:child_process';
import { readFile, writeFile, rm } from 'node:fs/promises';
import { promisify } from 'node:util';
import { createHash } from 'node:crypto';
import { checkDeterminism } from '../scripts/audit/check-determinism.mjs';

const execAsync = promisify(exec);

const REPORT_PATH = 'out/0.4/audit/report.json';

describe('audit', () => {
    before(async () => {
        // Clear previous report if it exists
        await rm(REPORT_PATH, { force: true });
    });

    it('should create a report and be deterministic', async () => {
        try {
            await execAsync('pnpm run audit');
        } catch (e) {
            assert.strictEqual(e.code, 1, 'Audit script should exit with code 1 when issues are found');
        }

        const reportContent1 = await readFile(REPORT_PATH, 'utf-8');
        const report1 = JSON.parse(reportContent1.trim());
        assert.strictEqual(typeof report1.ok, 'boolean', 'ok property should be a boolean');

        const hash1 = createHash('sha256').update(reportContent1).digest('hex');

        // Re-run audit
        try {
            await execAsync('pnpm run audit');
        } catch (e) {
            assert.strictEqual(e.code, 1, 'Audit script should exit with code 1 on second run');
        }

        const reportContent2 = await readFile(REPORT_PATH, 'utf-8');
        const hash2 = createHash('sha256').update(reportContent2).digest('hex');

        assert.strictEqual(hash1, hash2, 'Audit report should be byte-identical on a second run');
    });

    describe('checkDeterminism', () => {
        const tempFile = 'tests/temp-crlf-file.json';

        after(async () => {
            await rm(tempFile, { force: true });
        });

        it('should report CRLF issues', async () => {
            await writeFile(tempFile, 'hello\r\nworld');
            const issues = await checkDeterminism();
            const crlfIssue = issues.find(issue => issue.path === tempFile && issue.issue === 'has_crlf');
            assert.ok(crlfIssue, 'Should find a CRLF issue in the temp file');
            await rm(tempFile, { force: true });
        });
    });
});
