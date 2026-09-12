# Native backend interchange (parent-owned)

The parent serializes the actual typed `Witgen.Program` constructors; it does not use model evaluation to discover syntax. Wire format v1 mirrors the compiled Core API:

- Program `ret ref` -> `{"tag":"ret","ref":index}`.
- Program `let_ op args regions next` -> `{"tag":"let","op":OPCODE,"args":[indices],"regions":[REGION],"result":TYPE,"next":PROGRAM,"static":{...}}`.
- A REGION is `{"inputs":[TYPE],"output":TYPE,"body":PROGRAM}` and starts with exactly that newest-first input environment. Captures are explicit arguments chosen by the operation.
- TYPE is `"scalar"`, `"bool"`, `{"record":"Name","fields":[{"name":"field","type":TYPE},...]}`, or `{"list":TYPE}`. These are extension-owned sort encodings, not constructors of the generic Lean kernel.
- A module declares `name`, `domain` (`field17`, `nat`, or `word`), typed `inputs`, `output`, `body`, and the source circuit's explicit input/witness slot map. `domain` is the selected scalar representation; it is part of the physical type identity.

Opcodes initially supported by the Rust emitter:
`field.const`, `field.add`, `field.mul`, `field.eq`;
`nat.const`, `nat.add`, `nat.mul`, `nat.div`, `nat.mod`, `nat.eq`;
`word.const`, `word.add`, `word.mul`, `word.div`, `word.mod`, `word.eq`;
`record.make`, `record.get` (static field index);
`list.empty`, `list.push`;
`control.branch`, `control.map`, `control.fold`.

A branch's args are `[condition] ++ captures`; both regions receive captures. A map's args are `[list] ++ captures`; its region receives `[element] ++ captures`. A fold's args are `[list, initial] ++ captures`; its region receives `[element, accumulator] ++ captures`. Each construct binds one result at de Bruijn index zero for `next`. Region bodies are emitted as actual code blocks, not evaluated during compilation.

The native emitter fails closed on unsupported op/type/static data, bad names, reference bounds, argument/region types, or output mismatches. JSON decoder and Rust text emission are tested parts of the TCB unless a separate correspondence proof is supplied. Source-generated manifests/IR hashes must identify the actually executed artifact. Cargo uses arkworks for `field17`, GMP-backed rug::Integer for `nat`, and wrapping u64 arithmetic for `word`; partial div/mod providers reject zero. Nat->word certification requires input and intermediate bounds and cannot be inferred from successful serialization.
