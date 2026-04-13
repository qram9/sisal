# EINSUM: Einstein Summation for Sisal

## Motivation

The existing `INNERPRODUCT` intrinsic only handles rank ≤ 2 (dot product, matrix multiply). It has no path for batched matmul or general tensor contractions. Rather than add a `BATCHMATMUL` node and keep growing the opcode table, a single `EINSUM` node covers all of these and is the standard interface used by NumPy, PyTorch, JAX, and TensorFlow.

With `EINSUM` in place, `INNERPRODUCT` becomes syntactic sugar that lowers to the appropriate einsum subscript based on rank.

---

## Surface Syntax

```
EINSUM("subscript", A [, B [, C ...]])
```

- First argument: a string literal — the subscript in standard NumPy einsum notation
- Remaining arguments: one or more tensor operands (rank ≥ 0)
- Returns: a scalar or array depending on the output index specification

### Examples

```
% Dot product (rank-1 × rank-1 → scalar)
EINSUM("i,i->", u, v)

% Matrix multiply (rank-2 × rank-2 → rank-2)
EINSUM("ij,jk->ik", A, B)

% Matrix-vector multiply
EINSUM("ij,j->i", A, x)

% Vector-matrix multiply
EINSUM("i,ij->j", x, A)

% Batched matrix multiply (rank-3 × rank-3 → rank-3)
EINSUM("bij,bjk->bik", A, B)

% General batched matmul with arbitrary batch dims (ellipsis notation)
EINSUM("...ij,...jk->...ik", A, B)

% Outer product (rank-1 × rank-1 → rank-2)
EINSUM("i,j->ij", u, v)

% Trace of a matrix (rank-2 → scalar)
EINSUM("ii->", A)

% Transpose
EINSUM("ij->ji", A)

% Element-wise product then sum (triple contraction)
EINSUM("ijk,ijk->", A, B, C)
```

---

## Index String Grammar

```
subscript   ::= inputs "->" output
inputs      ::= index_spec ("," index_spec)*
index_spec  ::= label*
              | "..." label*      (* ellipsis = zero or more batch dims *)
output      ::= label*
              | "..." label*
              | ""               (* empty = scalar result *)
label       ::= 'a'..'z'
```

Rules:
- A label that appears in multiple inputs and is absent from the output is **contracted** (summed over).
- A label that appears in the output is **free** (kept).
- `...` in inputs expands to the same set of batch dimensions for all operands that use it. The batch shape is broadcast-compatible across operands.
- Implicit output (subscript without `->`) follows NumPy convention: all labels that appear exactly once, in alphabetical order.

---

## IF1 Node

**`EINSUM_NODE`** (opcode 127)

- **Inputs:** N ports, one per tensor operand
- **Output:** port 0, the result tensor (or scalar)
- **Pragma:** `Subscript(subscript_string)` — carries the index string to the backend

The subscript is stored as a `Subscript of string` pragma on the node. The backend is responsible for compiling the loop nest.

---

## Lowering Strategy

The compiler pattern-matches common subscripts to existing optimized nodes:

| Subscript | Emitted node | Notes |
|-----------|-------------|-------|
| `"i,i->"` | `DOT` | Result type: scalar |
| `"ij,jk->ik"` | `MATMUL` | Result type: same as A |
| `"ij,j->i"` | `MATVECMUL` | Result type: same as B |
| `"i,ij->j"` | `VECMATMUL` | Result type: same as A |
| anything else | `EINSUM_NODE` | Backend generates loop nest |

The general `EINSUM_NODE` path:
1. The backend parses the subscript string at compile time
2. Determines contraction and free indices
3. Expands `...` by querying runtime rank via `DV_NUM_RANK`
4. Generates a loop nest over all free and contracted indices
5. Accumulates the result into the output array

---

## `INNERPRODUCT` Compatibility

`INNERPRODUCT(A, B)` is now dispatched as follows:

| rank(A), rank(B) | Lowered to |
|-----------------|-----------|
| 1, 1 | `DOT` |
| 2, 2 | `MATMUL` |
| 2, 1 | `MATVECMUL` |
| 1, 2 | `VECMATMUL` |
| ≥ 3, ≥ 3 | `EINSUM_NODE("...ij,...jk->...ik")` |

This extends inner product to arbitrary rank without new opcodes.

---

## Result Type

- Output index string is empty (after stripping `...`): result is a scalar — `get_deep_elem_ty` of the first operand.
- Output index string is non-empty: result is `Array_dv(deep_elem_ty)`. Rank is implicit in the dope vector at runtime.

This is consistent with how `DV_RESHAPE` and broadcasting results are typed throughout the compiler.
