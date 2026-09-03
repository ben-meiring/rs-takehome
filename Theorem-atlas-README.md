# Theorem Atlas

The Theorem Atlas is an interactive map of the results, dependencies, open questions, and refuted hypotheses in the [`VerifiedMechanisms/rs-takehome`](https://github.com/VerifiedMechanisms/rs-takehome) repository.

**[Open the interactive Theorem Atlas](https://ben-meiring.github.io/rs-takehome/)**

## Features

- **Topic view:** Groups results by research area.
- **Dependency graphs:** Shows which earlier results each theorem uses and which later results depend on it.
- **Focused theorem view:** Displays a theorem together with its direct prerequisites and downstream applications.
- **Theorem statements:** The **Show exact theorem claim** button displays the full mathematical statement.
- **Proof links:** The **View proof** button opens the corresponding proof in the original repository.
- **Search:** Finds results by theorem number, title, or keyword.
- **Research goals:** Displays open problems and their relevant proof obligations.
- **Refuted hypotheses:** Separately records conjectures that have been disproved.
- **Formalization status:** Results marked **Lean certified** have corresponding machine-checked Lean formalizations.
- **Graph navigation:** Supports panning, zooming, resetting the view, and moving backward through previously opened views.

## How to use it

Begin on the **Topics** page and select a research area. This opens a dependency graph containing the principal results in that area.

Click any theorem to open its focused view. The theorem appears in the center, with its prerequisites on the left and its downstream uses on the right.

- **Show exact theorem claim** displays the full statement.
- **View proof** opens the proof in GitHub.
- **Back** returns to the previous view.
- **Show all results** expands beyond the landmark results.
- **Research goals** displays open directions.
- **Refuted hypotheses** displays unsuccessful conjectures.
- The search bar locates theorems by number, title, or keyword.
- The `+`, `−`, and **Reset view** controls adjust the graph view.

## Status conventions

- **Lean certified:** A corresponding Lean proof is available.
- **Refuted:** The proposed statement is false.
- **Research goal:** An open objective rather than an established theorem.
- **Dashed connections:** Inferred proof obligations or compressed relationships rather than direct dependencies asserted by the repository.

## Implementation

The published atlas is contained in [`index.html`](index.html). Its theorem data, styling, and interactive JavaScript are embedded directly in the file; KaTeX is loaded externally to render mathematical expressions.
