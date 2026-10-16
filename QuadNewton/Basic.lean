import Mathlib

/-!
# The complete quadrilateral: shared model

Four lines `L₁ L₂ L₃ L₄` in the plane `ℂ`, each given by a point and a nonzero direction.
`meet L M` is the intersection point of two non-parallel lines. The six vertices of the complete
quadrilateral are `meet Lᵢ Lⱼ`; its three diagonals join opposite vertices:
`(A₁₂, A₃₄)`, `(A₁₃, A₂₄)`, `(A₁₄, A₂₃)`. Omitting one line leaves a triangle.
This file is SHARED by the two Paper E developments and must not be changed.
-/

open Complex ComplexConjugate

namespace QuadNewton

/-- The cross product of two plane vectors, viewed as complex numbers. -/
noncomputable def cr (a b : ℂ) : ℝ := (conj a * b).im

/-- A line, given by a point `p` and a direction `d`. -/
structure Line where
  p : ℂ
  d : ℂ

/-- The points of a line. -/
def Line.carrier (L : Line) : Set ℂ := {z | cr L.d (z - L.p) = 0}

/-- The intersection point of two lines (meaningful when they are not parallel). -/
noncomputable def meet (L M : Line) : ℂ :=
  L.p + ((cr M.d (M.p - L.p) / cr M.d L.d : ℝ) : ℂ) * L.d

/-- Four lines in general position: nonzero directions, pairwise non-parallel,
no three through one point. -/
structure GenPos (L₁ L₂ L₃ L₄ : Line) : Prop where
  d₁ : L₁.d ≠ 0
  d₂ : L₂.d ≠ 0
  d₃ : L₃.d ≠ 0
  d₄ : L₄.d ≠ 0
  p12 : cr L₁.d L₂.d ≠ 0
  p13 : cr L₁.d L₃.d ≠ 0
  p14 : cr L₁.d L₄.d ≠ 0
  p23 : cr L₂.d L₃.d ≠ 0
  p24 : cr L₂.d L₄.d ≠ 0
  p34 : cr L₃.d L₄.d ≠ 0
  c123 : meet L₁ L₂ ∉ L₃.carrier
  c124 : meet L₁ L₂ ∉ L₄.carrier
  c134 : meet L₁ L₃ ∉ L₄.carrier
  c234 : meet L₂ L₃ ∉ L₄.carrier

/-- The circumcentre of the triangle `a b c` (explicit formula; meaningful for non-collinear points). -/
noncomputable def circ (a b c : ℂ) : ℂ :=
  a + (((Complex.normSq (b - a) : ℝ) : ℂ) * (c - a) - ((Complex.normSq (c - a) : ℝ) : ℂ) * (b - a)) /
    (conj (b - a) * (c - a) - (b - a) * conj (c - a))

/-- The orthocentre of the triangle `a b c`, via Euler's relation `H = a + b + c − 2O`. -/
noncomputable def ortho (a b c : ℂ) : ℂ := a + b + c - 2 * circ a b c

/-- The foot of the perpendicular from `z` to the line `L`. -/
noncomputable def foot (z : ℂ) (L : Line) : ℂ :=
  L.p + (((conj L.d * (z - L.p)).re / Complex.normSq L.d : ℝ) : ℂ) * L.d

end QuadNewton
