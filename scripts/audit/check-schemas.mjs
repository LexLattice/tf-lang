import { readdir, readFile } from 'node:fs/promises';
import { join } from 'node:path';
import Ajv from 'ajv';

const SCHEMAS_DIR = 'schemas';

/**
 * @returns {Promise<Array<{file: string, ok: boolean, errors?: any[]}>>}
 */
export async function checkSchemas() {
  const ajv = new Ajv({ allErrors: true });
  const files = await readdir(SCHEMAS_DIR);
  const schemaFiles = files.filter(f => f.endsWith('.json'));

  const schemas = [];
  for (const file of schemaFiles) {
    const filePath = join(SCHEMAS_DIR, file);
    const content = await readFile(filePath, 'utf-8');
    try {
      const schema = JSON.parse(content);
      schemas.push({ file: filePath, schema });
    } catch (e) {
      schemas.push({ file: filePath, schema: null, error: e });
    }
  }

  for (const { schema } of schemas) {
    if (schema && schema.$id) {
        try {
            ajv.addSchema(schema, schema.$id);
        } catch(e) {
            // ignore
        }
    }
  }

  const results = [];
  for (const { file, schema, error } of schemas) {
    if (error) {
      results.push({
        file,
        ok: false,
        errors: [ { message: `JSON parsing failed: ${error.message}` } ],
      });
      continue;
    }

    const schemaCopy = { ...schema };
    delete schemaCopy.$schema;

    try {
      const valid = ajv.validateSchema(schemaCopy);
      if (valid) {
        results.push({ file, ok: true });
      } else {
        results.push({ file, ok: false, errors: ajv.errors });
      }
    } catch (e) {
       results.push({ file, ok: false, errors: [ { message: e.message } ] });
    }
  }

  return results;
}
