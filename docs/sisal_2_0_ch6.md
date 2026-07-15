# Chapter 6 — FOR Expressions

*Transcribed from the Sisal 2.0 manual (`sisal_2_0.pdf`, Ch. 6, pp. 45–56 of the
manual / PDF pages 54–65), by rendering each page to an image and reading the glyphs
directly (the embedded OCR text layer is unreliable — mangles `π`, `[1..3]`, `≠`, etc.).*

This chapter describes SISAL's **for** expression, which uses either distribution of
control or iteration to produce one or more values. In some sense it resembles iteration
in conventional languages, but retains single assignment and functional semantics, and is
itself an expression that can appear within other expressions. The syntax follows:

```
for-exp        ::= [ for-top ]
                   for-body
                   for-bottom
for-top        ::= for in-exp-list [; [ decldef-part ] ] [ for-test ]
                 | for decldef-part [ for-test ]
                 | for-test
for-body       ::= do [ decldef-part ] [ for-test ]
for-bottom     ::= returns return-exp [, return-exp ] ···
                   end { for | while | until | do }
for-test       ::= { while | until } expression
return-exp     ::= stream of expression [ filter ]
                 | expression [ filter ]
                 | suffix ( value-id )
                 | array [ [ size-descriptor ] ] of expression
                       [ filter | at [ at-exp [, at-exp ] ··· ] ]
filter         ::= when expression
                 | unless expression
at-exp         ::= expression | ..
in-exp-list    ::= in-exp [ dot in-exp ] ···
                 | in-exp [ cross in-exp ] ···
in-exp         ::= value-id in expression [ at [ index-id-list ] ]
                 | value-id in [ triplet ]
index-id-list  ::= { .. | value-id } [, { .. | value-id } ] ···
```

Note that the scope of any value name defined in an enclosing construct is passed into the
**for** expression, but the value name may be re-established within the construct. The scope
of any value names introduced in the **for** expression is the entire construct textually
below its definition. That is, the **for** expression like all other constructs in SISAL must
obey the "definition before use" rule.

The **for** expression contains separate sections for value name initialization and
termination testing, distributed or repetitive action (the body), and result calculation.
The general strategy is to introduce some value names, and distribute them and all other
names visible to the **for** expression into one or more instances of the body, or
re-establish one or more of them during successive body executions. When the distributed
body invocations complete, or all termination criteria are met, or both, the sequences of
values produced by the body executions are passed to the results section for packaging. The
values can be packaged into arrays or streams, or combined using predefined reduction
operations (discussed in Chapter 9). It is possible to return the last value of a sequence, or
the last value meeting a particular criterion.

The **for** expression has three parts: a top, body, and bottom. The top part establishes
zero or more value names (each defined once) and optionally gives the body distribution or
iteration control logic. Providing control in the top part can prevent execution of the body
altogether, defining a **zero trip iteration form**. Note that the top part is optional, as it
is possible to provide a termination condition that executes after each body execution,
defining a post-test iteration form. It is possible to specify body distribution control and
iteration control in the same **for** expression, resulting in an iterative computation.

The body part (beginning with **do**) defines the actions to be carried out in either a
distributed or iterative manner. In the iterative form, the body can re-establish carried
values for the next iteration.

The bottom or **returns** part packages the values produced in the **for** body. **If the body
never executes, neither does the bottom part. In this case, the resulting values are the
default values of the various returns parts** (discussed in Section 6.2). The closing reserved
word of the **for** expression must match the reserved word introducing it: (**for**, **while**,
**until**, or **do**).

The following example illustrates a pre-test, iterative **for** expression, calculating π:

```sisal
for
    Approx := 1.0; Sign := 1.0; Denom := 1.0; i := 1
while i <= Cycles do
    Sign  := -Sign; Denom := Denom + 2.0;
    Approx := Approx + Sign / Denom;
    i     := i + 1
returns Approx * 4.0
end for
```

It returns the last value of `Approx` after multiplying it by 4.0.

The next example uses body distribution control instead of iteration control. It also
computes π, producing the same result if `Cycles` is even. The reduction `sum` is described
in Chapter 9.

```sisal
for i in [1..Cycles/2] do
    val := 1.0/real(4*i-3) - 1.0/real(4*i-1);
returns sum( val )
end for * 4.0
```

All the `val`s can be computed independently — the distributed control establishes
`Cycles/2` instances of the body, all safely parallel. In the absence of iterative control,
the number of body invocations can be determined by examining the distributed control parts.

---

## 6.1 Control

A **for** expression must have either body distribution or iteration control, and can have
both. Body distribution control is also referred to as an *in-expression list*. It can introduce
value names of type integer whose values are taken from arithmetic progressions, or value
names whose values represent the scattered components of arrays or streams of any type.

Iteration control (a boolean expression preceded by **while** or **until**) can appear just
before the body or right after it. Before the body ⇒ executes before each body execution
(pre-test); after ⇒ after each execution (post-test). A **while** stops when its expression is
**false**; an **until** stops when **true**.

It is illegal to have both pre-test and post-test iterative control in the same **for**. But
distribution and iteration control can coexist: then the body is executed iteratively, and the
number of iterations is bounded by both the distribution count and the iteration control.

### 6.1.1 Distribution Control

Optional, but if present must immediately follow **for**. It introduces one or more named
sets of integers from arithmetic progressions (*range triplets*) or elements from arbitrarily
typed array or stream values, or both. The scope of the names includes all following
distribution control parts (in a cross product), all iteration control parts, and all body and
result expressions, except when redefined in an inner scope. **Names defined this way may
not be redefined via assignment in the body.**

```
in-exp-list   ::= in-exp [ dot in-exp ] ···
                | in-exp [ cross in-exp ] ···
in-exp        ::= value-id in expression [ at [ index-id-list ] ]
                | value-id in [ triplet ]
index-id-list ::= { .. | value-id } [, { .. | value-id } ] ···
```

#### Range Triplets

A range triplet defines a named sequence of integer values from a triplet in square
brackets; each expression is optional and integer-typed. First two = lower/upper bounds;
third = stride (never zero, defines direction). Missing first ⇒ 1. Missing second ⇒ ±∞ per
the stride sign. Default stride = 1.

```sisal
I in [1..3]
J in [ ..3]
K in [3..100..2]
L in [100..98..-1]
M in [1..]
N in [..]
```

`I` above takes on 1, 2, 3; `L` takes 100, 99, 98. The following uses a triplet to sum the
integers between 1 and `N`:

```sisal
for I in [1..N] do returns sum(I) end for
```

If `N` is 3, it returns 1+2+3 = 6. Notice the body is empty.

#### Stream Scattering

```
in-exp ::= value-id in expression [ at [ index-id-list ] ]
         | value-id in [ triplet ]
```

The expression after **in** must be a stream. The optional **at** part is a value name that,
for each stream element, is the integer position of the element in the stream.

```sisal
for x in S do returns sum(x) end for   -- sums the elements of stream S
```

#### Array Scattering

Same syntax as stream scattering; the expression after **in** must be an array. If an **at**
part is provided, a value-id or empty triplet must be supplied **for each dimension** of the
scattered array. The **at** part gives the dimensionality of the scatter and introduces
additional value names — *scatter indices* — that take on the index positions of the scattered
values. In the absence of an **at** part, **all** dimensions are scattered (the element index
takes on all components). The empty-triplet version specifies that the entire associated
dimension is to be scattered.

This scatters planes from the second and third dimensions of `A` (a 3-D matrix):

```sisal
for X in A at [I,..,..] do
    ... X[..,..] ...
returns ...
end for
```

Here `X` is two-dimensional and `I` takes the successive indices of `A`'s first dimension.
This scatters all components of `A`:

```sisal
for X in A do              -- identical to "for X in A at [I,J,K] do"
    ... X ...
returns ...
end for
```

#### DOT and CROSS Products

```
in-exp-list ::= in-exp [ dot in-exp ] ···
              | in-exp [ cross in-exp ] ···
```

**dot** produces a *dot product* of in-expressions — all must yield the same number of values.

```sisal
for i in [1..2] dot j in [3..4] do
returns product(i+j)
end for
```

The dot product produces two index pairs, `[1,3]` and `[2,4]`, and the expression yields 24.

**cross** yields a Cartesian (outer) product; the in-expressions need not produce the same
number of values.

```sisal
for i in [1..2] cross j in [3..4] do
returns product(i+j)
end for
```

The cross product produces four pairs — `[1,3]`, `[1,4]`, `[2,3]`, `[2,4]` — and yields 600.
Triplet/element indices may be referenced in textually succeeding in-expressions of a cross
(the following yields 14400):

```sisal
for i in [1..2] cross j in [i..4] do
returns product(i+j)
end for
```

### 6.1.2 Iteration Control and Carried Values

```sisal
for
    I := 1
while I < 5 do
    K := I;
    I := I + 2;
    J := K + I;
returns product(I+J)
end for
```

Yields 91 = ((1+2)+(1+(1+2))) × ((3+2)+(3+(3+2))). Each carried value (here `I`) is
redefined exactly once in the body; conventional sequential execution describes each body.

The initial value of a carried value need not be defined in the top portion. The following is
legal and semantically equivalent (note it ends with **while**, not **for**):

```sisal
let
    I := 1
in
    while I < 5 do
        K := I;
        I := I + 2;
        J := K + I;
    returns product(I+J)
    end while, I          -- NOTE the reference to I, the I defined in the let part
end let
```

This yields `91, 1`. In general, a carried value may be explicitly initialized in the top part,
or **implicitly initialized merely by its use** — in the latter case the value with that name is
*copied* for use within the **for**; the exterior name is not changed. This lets already-defined
names (e.g. formal parameters) be used iteratively without spurious redefinition.

---

## 6.2 Result Values

The bottom or **returns** part executes once for each execution of the body, packaging the
results and returning them to the enclosing scope.

```
for-bottom     ::= returns return-exp [, return-exp ] ···
                   end { for | while | until | do }
return-exp     ::= stream of expression [ filter ]
                 | expression [ filter ]
                 | suffix ( value-id )
                 | array [ [ size-descriptor ] ] of expression
                       [ filter | at [ at-exp [, at-exp ] ··· ] ]
size-descriptor ::= [ value-id in ] triplet [, [ value-id in ] triplet ] ···
filter         ::= when expression | unless expression
at-exp         ::= expression | ..
```

A packaging part can build a stream (**stream of** / **suffix**), an array (**array of**), reduce a
sequence to a single value (a predefined reduction), or eliminate all but the last value of a
sequence and return that (**expression**, the "last value" part). The order of values in each
sequence is identical to the body execution order (a function of the control logic:
left-to-right across a triplet; dimension/subscript order for array scatter; component order
for stream scatter; left-to-right across cross in-expressions).

**If the body does not execute, the returned values are those defined by the default actions of
the various packaging parts. Note also that initial values for names of carried values do not
contribute to the results of a for expression.** As each body executes, new values are defined,
and these names may be used to define results.

### 6.2.1 Last Value

The **expression** or "last value" part yields the last value in a sequence, or reduces the
sequence into a single value by applying a predefined reduction. **The default value of this
packaging part is either an error value or the default value of the applied reduction** (refer
to Chapter 9).

```sisal
for I in [1..10] do
    J := I - 1;
returns I+9, J, sum(I+J)
end for
```

Yields `19, 9, 100`: the last `I` plus 9, the last `J`, and the sum of all the `(I+J)`s.

### 6.2.2 Stream of

Packages a sequence into a stream (order preserved). Returns integers 2, 3, 4 — so `S[2]`
yields 3:

```sisal
S := for i in [1..2] cross j in [i..2] do
     returns stream of i+j
     end for;
```

**The default value of the `stream of` part is an empty stream.**

Using **suffix**, one can return the portion of a stream *not* scattered by an in-expression
(cannot appear in a **for** with **cross** in-expressions). Its only parameter is the name of a
stream being scattered:

```sisal
for c in S
while ( c = ' ' ) do
returns sum(1), suffix(S)
end for
```

Returns the leading number of blanks in `S` and a stream of `S` minus the leading blanks. If
all scattered components contribute, the suffix stream is empty. If the body never executes,
the value returned is the original stream. (The first extant component of any stream is at
position 1.)

### 6.2.3 Array of

The **array of** part packages a sequence into an array. In the absence of an **at** part (a
position specifier), the ordering matches the sequence. The following returns a 1-D array of
integers 2, 3, 4 — `A[2]` yields 3:

```sisal
A := for i in [1..2] cross j in [i..2] do
     returns array of i+j
     end for;
```

Here the lower bound of `A` is 1 (the default).

Providing a **size descriptor** allows packaging multidimensional arrays. **Distributed names
or carried values may not be involved in the expressions giving array size.** In this
descriptor, the default lower bound of each triplet is 1, the upper bound may be omitted, the
stride is always 1 (the third triplet expression is never allowed), and named triplets are
never allowed. **If an upper bound is given, the extent is mandated** — the same number of
values must contribute. If one upper bound is supplied, they must be supplied for all
dimensions.

```sisal
let
    A := array integer [1..2,0..1: [1,..] 1, 2; [2,..] 3, 4];
    B := for I in [1..4] do
         returns array [1..2,0..1] of I
         end for
in
    A, B
end let
```

This builds two identical matrices. Values are placed in **subscript order** (left to right,
top to bottom): positions `[1,0]`, `[1,1]`, `[2,0]`, `[2,1]`.

In a **for** using iteration control and carried values, all contributing expression values
must have dimensionality **one smaller** than the descriptor and be the same size in all
dimensions. The extent of the first dimension comes from the number of iterations; the
remaining dimensions from the common extents of the contributing expressions. For a 1-D
result the contributing values may have any type; if arrays, they must share dimensionality
but may differ in extent ("ragged" arrays of arrays).

In a **for** using only distribution control, the dimensionality of the Cartesian product of
values scattered via **cross** and **at** need not match the array descriptor's dimensionality:

- **The descriptor may be absent or 1-D**, regardless of the scatter. For example:
  ```sisal
  for i in [1..2] cross j in [3..4]
  returns array of i*j
  end for
  ```
  builds the same array as the generator `array integer[ 3, 4, 6, 8 ]`. Contributing values
  may be any type; if arrays, same dimensionality but may differ in extent (ragged).

- **The descriptor may match the number of scattered items** — each corresponds to an
  associated array dimension, defining its extent; contributing values are single elements:
  ```sisal
  for x in A at [i,j]
      k := ...
  returns array[0..,0..] of g(x,k)
  end for
  ```
  defines a 2-D array whose extents are the numbers of `i` and `j` values, respectively.

- **The descriptor may be n-dimensional with k scatter dims, n > k** — the first k dims come
  from the scatter extents; the contributing values must be (n−k)-dimensional with identical
  extents, defining the last n−k dims (`g(x,k)` must produce 2-D arrays of identical extents):
  ```sisal
  for x in A at [i,j]
      k := ...
  returns array[0..,0..,1..,1..] of g(x,k)
  end for
  ```

The optional **at** part is semantically like the position specifiers of an array generator
(Chapter 4): it specifies where individual components are placed. **One and only one**
component can be defined for each position, and **the presence of an at part requires a size
descriptor that specifies the extents of all dimensions (upper bounds are not optional here).**
This builds an array of components 40, 30, 20, 10:

```sisal
T := for I in [1..4] do
     returns array [4..7] of I*10 at [4+I-1]
     end for
```

The lower bound of the result is 4. The next example places the vectors built within the
**for** body into successive rows of the matrix `M`:

```sisal
M := for I in [1..2] do
     V := for J in [1..2] do
          returns array of I + J
          end for;
     returns array [1..2,1..2] of V at [I,..]
     end for;
```

The number of parts of the position specifier must match the dimensionality of the generated
array. (See Chapter 4 for position specifiers and array-generation semantics.)

**In the absence of a size descriptor, the default value of an `array of` part is an empty
array if the body never executes. If a size descriptor is present, the default value is an
error value** (see Chapter 11).

### 6.2.4 Masking Filters

Except for the **suffix** operator, each **returns** part can be optionally followed by a
masking filter. **In array packaging, a masking filter is not allowed if an `at` part or size
descriptor is present, and makes sense only for one-dimensional arrays** (to preserve
rectangularity of multidimensional arrays). A masking filter is a boolean expression preceded
by **when** or **unless**:

```
filter ::= when expression
         | unless expression
```

If a **when** filter is false, or an **unless** filter is true, the corresponding sequence value
is dropped. The following generates a 1-D array of odd integers starting with 1:

```sisal
for I in [1..N] do
returns array of I when mod(I,2) ~= 0
end for
```
