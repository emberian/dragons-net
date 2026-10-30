# Compiler input

`dn-compiler compile FILE` prints a function given as JSON through the same gate as the built-in programs (`DN.Compiler.Input`). The examples in `examples/` are the region and copy kernels. The baseline lane prints the copy kernel it runs natively from `examples/echo.json`, which has to print as the built-in one too.

```sh
lake build dn-compiler
.lake/build/bin/dn-compiler compile examples/echo.json > echo.pnk
.lake/build/bin/dn-compiler compile examples/region.json > region.pnk
cake --pancake --reg_alg=0 --main_return=true < echo.pnk > echo.S
```

## Format

The file is one JSON object of version 1. It has the fields `dn_input`, the version; `function`, the exported function; and `calls`, the functions it calls, which may be left out. A field the format does not have is refused, so that a misspelt name is not silently dropped; a key given twice takes its last value.

A function is `{"name": N, "params": [names], "body": [statements]}`; every parameter and value is a 64-bit word, and arithmetic wraps. The exported function's name starts with `dn_`; every name is an identifier that is no keyword of either pinned lexer.

| Form | Meaning |
| --- | --- |
| `7`, `"x"`, `["@base"]` | A literal below 2^64, a local, the heap's base (refused in an exported function) |
| `[OP, a, b]` | `+ - * & \| ^ < <= ==`; `<` and `<=` compare signed |
| `[">>>", a, 3]`, `["<<", a, 3]` | Logical shifts by a literal below 64 |
| `["lds", 1, a]`, `["ld8", a]` | A word or a byte loaded from an address |
| `["var", x, e]`, `["set", x, e]` | A local declared, or assigned |
| `["st", a, e]`, `["st8", a, e]` | A word or a byte stored |
| `["if", e, [..], [..]]`, `["while", e, [..]]` | Both branches, which may be empty, and loops; a value other than zero is true |
| `["call", r, f, [args]]` | A function of `calls`, its result declared as `r` |
| `["return", e]` | The function's result; every path ends in one |
| `["ffi", name, [args]]` | Read, but refused in an exported function (DN0117) |

Addresses are byte addresses; a word is loaded and stored at an address the caller aligns, and bytes are little-endian. The caller owns every buffer: the gate checks scope and shape, not that an address is addressable, and an exported function takes at most four parameters.

## Refusals

A refused input prints `error[DNnnnn]: message` on stderr and ends with status 1 if the gate refused it, 3 if the input is not of the format; a file that cannot be read ends it with status 2. The codes do not change between releases; a new refusal gets a new code.

| Code | Refusal |
| --- | --- |
| DN0001 | Not JSON |
| DN0002 | Another version of the format |
| DN0003 | More than 256 KiB |
| DN0004 | More than 256 levels of JSON |
| DN0005 | A field the format does not have |
| DN0006 | Not of the format: a form, a type or a field missing where one is due |
| DN0100–DN0122 | The gate's reasons, one code each, in the order of `Checked.Reason`; DN0119 and DN0120 are another entry's and not printed here |

`tests/test_native.py` holds each code of the format and four of the gate's against an input that earns it, and both examples against the built-in programs.

## Versions

The version is the format's major version. A compiler reads its own and refuses any other with DN0002. A change that a reader of the old format would misread or refuse gets a new version, and since an unknown field is refused, so does a new field.
