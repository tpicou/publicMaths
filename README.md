# publicMaths

A collection of mathematical results, each with a complete written proof and, where possible, a machine-checked verification in [Lean 4](https://lean-lang.org/).

## Projects

| Project | Summary |
| --- | --- |
| [grau-ribas-conjecture](grau-ribas-conjecture) | Proof of Grau Ribas's conjecture $a_n\sim(2n/3)^{3/2}$ for the cube-root recurrence [OEIS A113768](https://oeis.org/A113768), with an explicit rate, a second-order expansion and the cubes in the sequence. Verified in Lean. |

## Layout

Each project lives in its own folder. A folder holds:

- a `README.md` with the results and how to check them;
- the write-up, as `proof.pdf` with its LaTeX source;
- if the project is formalised, its own Lean project, with Lean and mathlib pinned for that project. Older projects keep building even as newer ones move to newer versions of mathlib.

To check a formalised project, go into its folder and follow its README, typically:

```sh
cd <project-folder>
lake exe cache get
lake build
```

## License

[MIT](LICENSE)
