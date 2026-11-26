# publicMaths

Mathematical results with complete written proofs and machine-checked Lean 4 verifications.

## Projects

| Project | Folder | Status |
| --- | --- | --- |
| Grau Ribas's conjecture for the cube-root recurrence [OEIS A113768](https://oeis.org/A113768) | [research/grau-ribas-2024](research/grau-ribas-2024) | Proved and verified in Lean, with explicit rate and second-order expansion ([PDF](research/grau-ribas-2024/proof.pdf)) |

Each project folder under `research/` has a README and a PDF write-up. The Lean proofs live in the `Maths/` library, because Lean's build tool `lake` builds from there; each project README links to its Lean files.

## Repository layout

```
research/<project>/   README, proof.pdf and proof.tex for each project
Maths/                Lean 4 library (one subfolder per project)
Maths.lean            build entry point and axiom audit
lakefile.lean         Lean project file; mathlib is pinned in lake-manifest.json
```

## Building the Lean proofs

```sh
lake exe cache get   # download prebuilt mathlib
lake build           # check every proof
```

## License

[MIT](LICENSE)
