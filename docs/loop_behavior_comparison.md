# Loop Behavior Comparison: Sisal vs. C vs. Fortran

This document explains the semantic differences in loop execution, loop variable updates, and value gathering between Sisal's sequential (`for initial`) loop and traditional loops in C and Fortran. 

---

## 1. Sisal's `for initial` Iteration Semantics

Sisal's `for initial` construct is a functional state-transition loop rather than a control-flow jump. Understanding it requires recognizing two core rules:

### Rule 1: The `initial` state is always evaluated and gathered (No Undefined States)
Sisal has a strict single-assignment policy. A `for initial` sequence defines a value history that must begin with a defined initial state (`body_0`). This initial state is unconditionally evaluated and added to any returns accumulation (like `returns stream of I` or `returns array of I`) before any loop condition check occurs. 

Even in a "zero-trip" loop where the loop guard is false on entry, the initial seed value is gathered. Because the `initial` subgraph is always executed:
* There is **never** a risk of accessing an uninitialized or undefined loop variable.
* An initial value is guaranteed to exist.

In contrast, in traditional C, if a loop accumulator or state variable relies on the loop body to obtain its value, and the loop executes 0 times, the variable remains empty or, worse, **uninitialized (undefined/garbage value)** if not manually initialized beforehand.

### Rule 2: The final out-of-bound `I` is always computed and gathered
In Sisal, the loop body executes to compute the *new* state of loop variables from the *old* state:
```sisal
I := old I + step;
```
If the loop condition is satisfied, the body executes, calculates the new value of `I`, and immediately gathers it. Because of this, **the final value of `I` (which fails the subsequent condition check and terminates the loop) has already been computed and is gathered**. Any expression in the `returns` clause using `I` will see this final out-of-bounds value.

---

## 2. Behavioral Contrast: Sisal vs. C vs. Fortran

Let's compare the behavior of these loops under two scenarios: a **zero-trip loop** and a **normal loop**.

### Scenario A: Zero-Trip Loop (Initial value is out-of-bounds on entry)
* **Sisal**: Initial seed is `10`. Condition is `I < 5`.
* **C**: Initial index is `10`. Condition is `i < 5`.
* **Fortran**: Initial index is `10`. Bound is `5`.

| Language | Example Code | Execution Details | Resulting Collection / Final Value / Undefined Risk |
| :--- | :--- | :--- | :--- |
| **Sisal** | ```sisal<br>for initial<br>  I := 10;<br>while I < 5 repeat<br>  I := old I + 1;<br>returns stream of I<br>end for<br>``` | `initial` executes unconditionally and gathers `10`. The condition `10 < 5` is evaluated, fails, and the loop terminates. | **Stream**: `[10]` (Size 1)<br>**Final `I`**: `10`<br>**Undefined Risk**: **None**. `I` is safely defined. |
| **C / C++** | ```cpp<br>int result; // Uninitialized!<br>for (int i = 10; i < 5; i++) {<br>  result = i; // Never runs!<br>}<br>// Using 'result' here is UNDEFINED!<br>``` | The condition `10 < 5` is checked first. Since it is false, the loop body never runs. `result` remains uninitialized. | **Vector / Accumulator**: `[]` (Empty)<br>**Final `i`**: `10`<br>**Undefined Risk**: **High**. Reading `result` yields garbage or crashes. |
| **Fortran** | ```fortran<br>INTEGER :: I, RESULT<br>! RESULT is uninitialized<br>DO I = 10, 5<br>  RESULT = I ! Never runs<br>END DO<br>``` | The trip count `MAX(0, (5 - 10 + 1))` evaluates to `0`. The loop body never runs. | **Final `I`**: `10`<br>**Undefined Risk**: **High**. Reading `RESULT` yields undefined values. |

---

### Scenario B: Normal Loop (5 iterations)
* **Sisal**: Initial seed is `1`. Condition is `I <= 5`.
* **C**: Initial index is `1`. Condition is `i <= 5`.
* **Fortran**: Loop range is `1` to `5`.

| Language | Example Code | Step-by-Step State Sequence | Resulting Collection / Final Value |
| :--- | :--- | :--- | :--- |
| **Sisal** | ```sisal<br>for initial<br>  I := 1;<br>while I <= 5 repeat<br>  I := old I + 1;<br>returns stream of I<br>end for<br>``` | 1. `initial` gathers `1`. (`body_0`) <br>2. `1 <= 5` is true: computes `2`, gathers `2`. (`body_1`) <br>3. `2 <= 5` is true: computes `3`, gathers `3`. (`body_2`) <br>4. `3 <= 5` is true: computes `4`, gathers `4`. (`body_3`) <br>5. `4 <= 5` is true: computes `5`, gathers `5`. (`body_4`) <br>6. `5 <= 5` is true: computes `6`, gathers `6`. (`body_5`) <br>7. `6 <= 5` is false: **exits**. | **Stream**: `[1, 2, 3, 4, 5, 6]` (Size 6)<br>**Final `I`**: `6` |
| **C / C++** | ```cpp<br>std::vector<int> vec;<br>for (int i = 1; i <= 5; i++) {<br>  vec.push_back(i);<br>}<br>``` | 1. `i = 1`: `1 <= 5` is true $\rightarrow$ pushes `1`, increments to `2`. <br>2. `i = 2`: `2 <= 5` is true $\rightarrow$ pushes `2`, increments to `3`. <br>3. `i = 3`: `3 <= 5` is true $\rightarrow$ pushes `3`, increments to `4`. <br>4. `i = 4`: `4 <= 5` is true $\rightarrow$ pushes `4`, increments to `5`. <br>5. `i = 5`: `5 <= 5` is true $\rightarrow$ pushes `5`, increments to `6`. <br>6. `i = 6`: `6 <= 5` is false $\rightarrow$ **exits**. | **Vector**: `[1, 2, 3, 4, 5]` (Size 5)<br>**Final `i`**: `6` |
| **Fortran** | ```fortran<br>INTEGER :: I<br>DO I = 1, 5<br>  ! Body executes for I = 1,2,3,4,5<br>END DO<br>``` | The trip count `5 - 1 + 1 = 5` is computed on entry. The loop runs exactly 5 times, and at the end of the last iteration, `I` is incremented to `6` before the loop exits. | **Final `I`**: `6` |

---

## 3. Comparison Summary

1. **The Out-of-Bounds Value**:
   * In both C and Fortran, the loop index variable ends up with the out-of-bounds value (`6`), but this value is **not** pushed or processed because the loop exits.
   * In Sisal, since the loop body computes the new state *before* testing the condition, the out-of-bounds value (`6`) is actually computed *inside* the loop body on the 5th iteration. Because it was computed by an executed loop body, **it is gathered into the stream/array**.

2. **Collection Sizes**:
   * For $N$ successful condition checks, a C loop yields $N$ elements.
   * A Sisal `for initial` loop yields $N + 1$ elements (the unconditional initial seed + $N$ body computations).

3. **Initialization Safety**:
   * Sisal enforces that loop-carried value streams always contain at least the `initial` seed value, eliminating uninitialized or undefined read states. 
   * C/Fortran loops running 0 times bypass body assignments completely, leading to undefined or garbage values if variables are read downstream without separate pre-loop initialization.
