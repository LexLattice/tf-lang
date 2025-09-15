Oracles Core (TS)

Result schema

```
type Result = {
  ok: boolean;
  code?: string;        // machine code
  message?: string;     // human message
  path?: string;        // RFC6901 JSON Pointer to offending value
  evidence?: unknown;   // optional structured evidence for diagnosis
}
```

Codes → messages

- E_NOT_EQUAL — values are not equal
- E_NOT_SUBSET — object is not a subset of expected
- E_OUT_OF_RANGE — value is out of range
- E_REGEX_MISMATCH — value does not match regex
- E_EMPTY — value is empty
- E_FIELD_UNKNOWN — unknown field present

Examples

- equals({a:1},{a:2}) → { ok:false, code:E_NOT_EQUAL, path:"/a" }
- subsetOf({a:1,x:1},{a:1}) → { ok:false, code:E_FIELD_UNKNOWN, path:"/x" }
- inRange(0,1,10) → { ok:false, code:E_OUT_OF_RANGE, path:"/", evidence:{min:1,max:10,actual:0}}
- matchesRegex("abc",/^\d+$/) → { ok:false, code:E_REGEX_MISMATCH, path:"/" }
- nonEmpty("") → { ok:false, code:E_EMPTY, path:"/" }

