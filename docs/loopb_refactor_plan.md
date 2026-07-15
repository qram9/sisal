# LoopB Refactoring Plan (Rumbaugh/Dennis Data Flow)

This document outlines the strategy for correcting the `LoopB` (`for initial`) lowering in the Sisal compiler to strictly follow data flow principles.

## 1. The `MERGE` Node
To distinguish loop selection from conditional `IF` selection, we use a `MERGE` node (ID 131) instead of the standard `SELECT` node.

- **Port 0**: Control signal (Boolean). `True` for the first iteration, `False` for subsequent iterations.
- **Port 1**: Initial value (from `INIT` graph).
- **Port 2**: Feedback value (from the end of the previous `BODY` iteration).

## 2. INIT Graph Strategy
The `INIT` graph must explicitly export all carry variables and their "OLD" counterparts.

- For $N$ carry variables (e.g., `I`, `A`, `B`, `PIVR`):
    - Export current values to ports `0` to `N-1`.
    - Export `OLD` counterparts (initial values) to ports `N` to `2N-1`.
- This ensures the `BODY` receives a complete state descriptor for the first iteration.

## 3. BODY Graph Strategy
The `BODY` graph acts as the cycle in the Rumbaugh model.

### 3.1 Input Ports
- **Port 0**: `is_first_iteration` control signal.
- **Ports 1 to 2N**: Incoming values from `INIT` (initial) or `BODY` outputs (feedback).

### 3.2 Selection Logic (The PHI-equivalent)
Inside the `BODY`, every carry variable `X` and its counterpart `OLD X` is defined by a `MERGE` node:
- `MERGE_X`: `(Control, INIT:X, Feedback_X)`
- `MERGE_OLD_X`: `(Control, INIT:OLD_X, Feedback_OLD_X)`

### 3.3 Induction and Shifting
When a variable is updated (e.g., `I := old I + 1`):
- The result of `old I + 1` becomes the "Current" value for the next iteration.
- The "Current" value of the *previous* iteration (the output of `MERGE_I`) becomes the "OLD" value for the next iteration.
- **Feedback Wiring**:
    - `BODY:Current_X_Output` -> `BODY:Feedback_X_Input`
    - `BODY:MERGE_X_Output` -> `BODY:Feedback_OLD_X_Input` (This implements the temporal shift).

## 4. Wiring and Implementation
- **Bypass Helpers**: Do not use `add_comp_node` or `wire_all_syms_to_compound`.
- **Manual Wiring**: Use low-level `If1.add_edge2` to connect specific ports.
- **Symbol Table**: Manually populate the `BODY` symtab with the outputs of the `MERGE` nodes to ensure `I` and `OLD I` resolve correctly in nested scopes.
