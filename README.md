# Theorem Atlas

Interactive map of the theorem dependencies, research frontiers, research goals,
and refuted hypotheses in the `VerifiedMechanisms/rs-takehome` repository.

## Run locally

The generated interface is already included. Open `theorem-atlas.html` in a web
browser, or serve the folder locally:

```bash
python3 -m http.server 8000
```

Then visit `http://localhost:8000/theorem-atlas.html`.

## Rebuild

Node.js is the only build dependency:

```bash
node build-theorem-atlas.js
```

The generator reads `data/theorem_index.json` and overwrites
`theorem-atlas.html`. Replace that JSON file with a newly generated theorem index
to update the atlas.

## Files

- `build-theorem-atlas.js`: interface generator and graph configuration.
- `data/theorem_index.json`: extracted theorem metadata and citations.
- `theorem-atlas.html`: generated single-page interface.

The “View proof” buttons link to the corresponding Markdown files in the public
GitHub repository; proof text is not copied into the interface.
