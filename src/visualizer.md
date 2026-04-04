This visualizer is a bridge between a high-level compiler representation (OCaml) and a low-level interactive debugger (Web). It takes your **IF1 (Intermediate Form 1)** graph and turns it into a navigable, hierarchical tree with live dataflow rendering.

Here is the step-by-step breakdown of how the engine works.

---

## 1. The Data Foundation (JSON)

Before any JavaScript runs, the OCaml side encodes your entire compiler state into a nested JSON object called `data`.

* **Nodes**: Contains the IDs, Labels (Math ops like `CMULT`), and nested sub-graphs.
* **Edges**: Two separate lists (`data_edges` and `error_edges`) to differentiate the "Happy Path" from your "Railway Monad."
* **Symtab/TypeMap**: Contextual data used for the right-hand sidebar.
* **AST**: The pretty-printed source origin you added for FFT debugging.

---

## 2. Step 1: Building the Hierarchy (`buildTree`)

The heart of the visualizer is a recursive function called `buildTree`.

* **How it works**: It looks at the current graph level. For every node, it creates a `<div>`.
* **Recursion**: If a node is a `Compound` node (like a `SELECT` or `LOOP`), `buildTree` calls itself. This creates the "Russian Doll" effect where you can keep diving deeper into nested scopes.
* **The HTML `<details>` tag**: We use native HTML summary/details tags. This is what allows you to "fold" everything except the root by default.

---

## 3. Step 2: Context Sync (`updateRightPane`)

Whenever you click a **Graph Summary** (the blue text that says `Graph {X nodes}`), an `onclick` event triggers `updateRightPane`.

1. **AST Update**: It checks if you have a **Pin** active. If not, it replaces the content of the bottom-right pane with the `ast` string of the graph you just clicked.
2. **Tab Switching**: It checks if you are on the "Symbols" or "TypeMap" tab and populates the top-right pane accordingly.
3. **Scoped View**: Because `currentGraph` is updated on every click, the sidebar always shows the symbol table for the *specific* loop or function you are currently looking at.

---

## 4. Step 3: Smart Highlighting (`selectionchange`)

This is the "Notepad++" feature.

* **The Listener**: The script listens for any text selection made by your mouse.
* **The Walker**: It uses a `TreeWalker` to scan every single piece of text currently visible in the browser.
* **The Highlight**: If it finds a match, it wraps that text in a `<mark>` tag.
* *Usecase:* If you select `Node 42` in the AST pane, every edge in the graph referring to `Node 42` turns yellow instantly.



---

## 5. Step 4: The Layout Engines (Resizers)

The visualizer uses a **CSS Grid** with two sets of "Resizer" logic:

* **Vertical Resizer**: Tracks your mouse `X` position. It updates the `--sidebar-width` CSS variable, causing the hierarchy to shrink and the sidebar to grow.
* **Horizontal Resizer**: Tracks your mouse `Y` position within the right-hand pane. It updates the `--ast-height` variable, allowing you to give the AST pane more or less room.
* **`userSelect = 'none'`**: While you are dragging, we disable text selection so you don't accidentally highlight half the screen while trying to move a bar.

---

## 6. Step 5: The DAG Renderer (`mermaid.js`)

When you click **Render DAG 🎨**, the visualizer transforms your textual edges into a visual diagram.

1. **Translation**: It iterates through `data_edges` and writes a Mermaid-compatible string (e.g., `N1 -- "p0->p1" --> N2`).
2. **Injection**: It places this string into a hidden modal window.
3. **Rendering**: It calls `mermaid.run()`. Mermaid parses that text and generates a high-performance **SVG** (Scalable Vector Graphic).
4. **Display**: The modal is set to `display: block`, showing you the visual dataflow topology of your FFT butterfly.

