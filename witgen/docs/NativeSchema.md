# Native Backend Interchange

The parent serializes the actual typed `Witgen.Program` constructors; it does not use model evaluation to discover syntax. Wire format v1 mirrors the compiled Core API:

- Program `ret ref` -> `{"tag":"ret","ref":index}`.
- Program `let_ op args regions next` -> `{"tag":"let","op":OPCODE,"args":[indices],"regions":[REGION],"result":TYPE,"next":PROGRAM,"static":{...}}`.
- A REGION is `{"inputs":[TYPE],"output":TYPE,"body":PROGRAM}` and starts with exactly that newest-first input environment. Captures are explicit arguments chosen by the operation.
- TYPE is `"scalar"`, `"bool"`, `{"record":"Name","fields":[{"name":"field","type":TYPE},...]}`, or `{"list":TYPE}`. These are extension-owned sort encodings, not constructors of the generic Lean kernel.
- A module declares `name`, `domain` (`bn254`, `nat`, `word`, or the bounded-regression `field17`), typed `inputs`, `output`, `body`, and the source circuit's explicit input/witness slot map. `domain` selects the scalar representation; it is part of physical type identity.
- BN254 modules use scalar TYPE `"scalar"`, `input_semantics: "bn254"`, and an exact decimal-string `field_modulus` matching BN254 Fr. The writer uses `wire_layout.field: "bn254"`. Full-width inputs, literals and output cells are decimal strings, never floating point or truncated u64 values. A BN254 source domain cannot be silently lowered to the `word` backend.

Opcodes initially supported by the Rust emitter:
`field.const`, `field.add`, `field.mul`, `field.eq`;
`nat.const`, `nat.add`, `nat.mul`, `nat.div`, `nat.mod`, `nat.eq`;
`word.const`, `word.add`, `word.mul`, `word.div`, `word.mod`, `word.eq`;
`record.make`, `record.get` (static field index);
`list.empty`, `list.push`;
`control.branch`, `control.map`, `control.fold`.

A branch's args are `[condition] ++ captures`; both regions receive captures. A map's args are `[list] ++ captures`; its region receives `[element] ++ captures`. A fold's args are `[list, initial] ++ captures`; its region receives `[element, accumulator] ++ captures`. Each construct binds one result at de Bruijn index zero for `next`. Region bodies are emitted as actual code blocks, not evaluated during compilation.

The native emitter fails closed on unsupported op/type/static data, bad names, reference bounds, argument/region types, or output mismatches. JSON decoding and Rust text emission are tested parts of the TCB unless a separate correspondence proof is supplied. Source-generated manifests/IR hashes identify the executed artifact. Cargo uses Arkworks for BN254 (four-limb Fp256) and the small regression field, GMP-backed `rug::Integer` for Nat, and wrapping u64 arithmetic for Word. Partial division/remainder reject zero. Nat→Word certification needs input/intermediate bounds, not merely successful serialization.

Generic `StructOp` schemas serialize to `record.make/get` without record-specific operation tags. Caller-owned sort universes can use `Export.moduleJsonWith`; the custom split example actually lowers a native circuit record to a structural field-list representation before export. Nested records preserve their descriptors' names and order.

Generated functions/writers/dispatch and fallible native providers return `witgen_native::Result<T>`, fixed to the enum `witgen_native::Error`. It implements `Display` and `std::error::Error`; original parsing/JSON/I/O errors remain accessible through `source()`. No catch-all string-error conversion is used. The JSONL CLI formats only the final diagnostic as `error`, alongside a stable `error_code`; Rust clients can match enum variants and structured payloads directly.
