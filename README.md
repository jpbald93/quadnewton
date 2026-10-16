# The complete quadrilateral in Lean 4: Newton–Gauss line, orthocentre line, Gauss–Bodenmiller

For four lines in general position: the midpoints of the three diagonals are collinear (Newton–Gauss line); the orthocentres of the four triangles are collinear and not all equal; each orthocentre has equal power with respect to the three circles on the diagonals as diameters (Gauss–Bodenmiller); and the orthocentre line is perpendicular to the Newton–Gauss line. With bridges to Mathlib's lines, intersections, circumcentres, orthocentres, power of a point and parallelism.

This repository is one of two Lean 4 developments accompanying the paper *The complete quadrilateral in
Lean 4: Newton–Gauss, Bodenmiller, the Miquel point, the Steiner circle and the Simson line* (J. Bald,
2026). The two developments share one file of definitions (`QuadNewton/Basic.lean`, identical up to its
namespace). The paper states each theorem in prose with every hypothesis and reports the verification
summarised below.

**Status:** all statements proved, no `sorry`. `gate.sh` checks **35** named declarations.

## Main statements

| Lean name | File:line | Statement |
|---|---|---|
| `QuadNewton.newton_gauss` | `QuadNewton/Quad.lean:53` | the three diagonal midpoints are collinear |
| `QuadNewton.diag_midpoints_ne` | `QuadNewton/Quad.lean:70` | two of the diagonal midpoints are distinct |
| `QuadNewton.orthocentres_collinear` | `QuadNewton/Quad.lean:79` | the four orthocentres are collinear |
| `QuadNewton.orthocentres_not_all_eq` | `QuadNewton/Quad.lean:97` | the four orthocentres are not all equal (no fixed pair need differ) |
| `QuadNewton.bodenmiller` | `QuadNewton/Quad.lean:135` | Gauss–Bodenmiller: equal powers w.r.t. the three diagonal circles |
| `QuadNewton.orthocentre_line_perp` | `QuadNewton/Quad.lean:155` | orthocentre line ⟂ Newton–Gauss line |
| `QuadNewton.pw_eq_power` | `QuadNewton/Bridge.lean:232` | local power of a point = Mathlib `Sphere.power` |
| `QuadNewton.ortho_eq_orthocenter` | `QuadNewton/Bridge.lean:140` | local orthocentre = Mathlib `Affine.Triangle.orthocenter` |

Every theorem assumes only that the four lines are in general position (`GenPos`: nonzero directions,
no two parallel, no three concurrent). Read the Lean statement for the exact form.

## Verification

`./gate.sh` builds the library and runs `#print axioms` on the 35 declarations in its `REQUIRED`
list. It fails if a source file contains `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
`set_option`, a macro or syntax extension; if the build fails; or if any listed declaration depends on
anything other than `propext`, `Classical.choice` and `Quot.sound`.

Expected output: `PASS (35 declarations, standard axioms only)`. Checked on x86-64 Linux and arm64
macOS at the pinned Mathlib revision.

`bash tests/tamper.sh` plants defects in scratch copies (ax2line, evalfake, falsehyp, macro, sorry, wrap) and checks that the gate
rejects each one.

The paper also reports a statement-level battery (conclusion mutations, contradiction probe,
satisfiability witnesses, hypothesis ablation, unused-variable linter), a blind re-formalisation of
the statements from the paper's prose with a Lean equivalence check, an independent numerical re-check,
and a prior-art search. Those results, and their limits, are in the paper's Verification section.

## Build

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get
lake build
./gate.sh
bash tests/tamper.sh
```

Toolchain: Lean `v4.33.1`, Mathlib (revision pinned in `lake-manifest.json`). `gate.sh` never fetches:
run `lake exe cache get` first.

## Note on how this was produced

The formal proofs and documentation were developed with the help of large-language-model AI
assistants. The author directed the work, reviewed the statements, and is responsible for the result.
The Lean kernel checks every proof.

## License

Code: Apache License 2.0 (see `LICENSE`). Documentation: CC BY 4.0.
