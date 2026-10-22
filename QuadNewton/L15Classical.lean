import QuadNewton.Basic
import QuadNewton.Lines
import QuadNewton.Core
import QuadNewton.Quad
import QuadNewton.Bridge
import QuadNewton.L14Newton

/-!
# Layer 15: classical reference statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

The writer's file used the namespace `ClassicalQuadrilateral`; here it is `QuadNewton.Classical`.
Each `cov_X` theorem has exactly the statement of the writer's `classical_X` (only the name and
the proof differ). The two construction obligations (`Configuration.vertex_exists_unique`,
`Configuration.triangle_independent`) keep the writer's statements and receive proofs. The
blocks marked "comparer" (the bridge `rl`, `genPos`, `vertex_eq`, ... and the lemmas before
the `cov_*` theorems) were added to connect the classical definitions to this development.

Writer's original header:
-/

/-!
Classical-source reconstruction of E1--E8 from writer_brief.txt alone.
Points are complex numbers, regarded as the real Euclidean affine plane.
All theorem proofs are intentionally omitted. No source-paper definitions or
statements have been consulted.

The two anchors for each line are merely a representation of an arbitrary
Euclidean line; they are not additional quadrilateral vertices or hypotheses.
-/

namespace QuadNewton.Classical

noncomputable section

/-- OWN DEFINITION: a genuine affine line, using Mathlib's affine span. -/
def IsLine (s : AffineSubspace ℝ ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ s = line[ℝ, a, b]

/-- OWN DEFINITION: four lines in general position, represented by two distinct anchors each.
`nonparallel` and `noTriple` are exactly the two general-position requirements.
No orientation, ordering around a polygon, or metric normalization is imposed.
-/
structure Configuration where
  anchorA : Fin 4 → ℂ
  anchorB : Fin 4 → ℂ
  anchors_distinct : ∀ i, anchorA i ≠ anchorB i
  nonparallel : ∀ i j, i ≠ j →
    ¬ AffineSubspace.Parallel (line[ℝ, anchorA i, anchorB i])
      (line[ℝ, anchorA j, anchorB j])
  noTriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ p : ℂ,
    ¬ (p ∈ line[ℝ, anchorA i, anchorB i] ∧
       p ∈ line[ℝ, anchorA j, anchorB j] ∧
       p ∈ line[ℝ, anchorA k, anchorB k])

namespace Configuration

/-- The represented lines; the geometry uses Mathlib affine subspaces. -/
def carrier (Q : Configuration) (i : Fin 4) : AffineSubspace ℝ ℂ :=
  line[ℝ, Q.anchorA i, Q.anchorB i]

/-! ### L15 bridge (inserted by the comparer; not part of the classical text)
Configuration line `i` as a repository `QuadNewton.Line`. -/
def rl (Q : Configuration) (i : Fin 4) : QuadNewton.Line := ⟨Q.anchorA i, Q.anchorB i - Q.anchorA i⟩

lemma rl_d_ne (Q : Configuration) (i : Fin 4) : (Q.rl i).d ≠ 0 :=
  sub_ne_zero.2 (Q.anchors_distinct i).symm

lemma rl_line (Q : Configuration) (i : Fin 4) :
    line[ℝ, (Q.rl i).p, (Q.rl i).p + (Q.rl i).d] = Q.carrier i := by
  simp [rl, carrier]

lemma mem_rl (Q : Configuration) (i : Fin 4) (z : ℂ) : z ∈ (Q.rl i).carrier ↔ z ∈ Q.carrier i := by
  rw [QuadNewton.carrier_eq_line _ (Q.rl_d_ne i), rl_line]; rfl

lemma rl_cr_ne (Q : Configuration) {i j : Fin 4} (hij : i ≠ j) :
    QuadNewton.cr (Q.rl j).d (Q.rl i).d ≠ 0 := by
  intro h0
  have := (QuadNewton.parallel_iff_cr (Q.rl_d_ne j) (Q.rl_d_ne i)).2 h0
  unfold QuadNewton.Line.toAffine at this
  simp only [rl_line] at this
  exact Q.nonparallel j i (Ne.symm hij) this

lemma genPos (Q : Configuration) : QuadNewton.GenPos (Q.rl 0) (Q.rl 1) (Q.rl 2) (Q.rl 3) := by
  rw [QuadNewton.genPos_iff]
  simp only [QuadNewton.Line.toAffine, rl_line]
  refine ⟨⟨Q.rl_d_ne 0, Q.rl_d_ne 1, Q.rl_d_ne 2, Q.rl_d_ne 3⟩,
    ⟨Q.nonparallel 0 1 (by decide), Q.nonparallel 0 2 (by decide), Q.nonparallel 0 3 (by decide),
     Q.nonparallel 1 2 (by decide), Q.nonparallel 1 3 (by decide), Q.nonparallel 2 3 (by decide)⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨z, h⟩; exact Q.noTriple 0 1 2 (by decide) (by decide) (by decide) z h
  · rintro ⟨z, h⟩; exact Q.noTriple 0 1 3 (by decide) (by decide) (by decide) z h
  · rintro ⟨z, h⟩; exact Q.noTriple 0 2 3 (by decide) (by decide) (by decide) z h
  · rintro ⟨z, h⟩; exact Q.noTriple 1 2 3 (by decide) (by decide) (by decide) z h

/-- CONSTRUCTION OBLIGATION: distinct, nonparallel planar lines meet uniquely.
This is derived from the configuration, not an extra input hypothesis. -/
theorem vertex_exists_unique (Q : Configuration) (i j : Fin 4) (hij : i ≠ j) :
    ∃! p : ℂ, p ∈ Q.carrier i ∧ p ∈ Q.carrier j := by
  refine ⟨QuadNewton.meet (Q.rl i) (Q.rl j), ?_, fun p hp => ?_⟩
  · have := (QuadNewton.meet_eq_iff (Q.rl_cr_ne hij) _).2 rfl
    exact ⟨(Q.mem_rl i _).1 this.1, (Q.mem_rl j _).1 this.2⟩
  · exact (QuadNewton.meet_eq_iff (Q.rl_cr_ne hij) p).1 ⟨(Q.mem_rl i _).2 hp.1, (Q.mem_rl j _).2 hp.2⟩

/-- OWN DEFINITION: the vertex is specified by incidence, not coordinates. -/
noncomputable def vertex (Q : Configuration) (i j : Fin 4) (hij : i ≠ j) : ℂ :=
  Classical.choose (Q.vertex_exists_unique i j hij)

/-- OWN DEFINITION: the three opposite-vertex pairs, each partitioning {0,1,2,3}.
The proof terms only certify that the two labels defining a vertex differ. -/
noncomputable def diagonalEndpoints (Q : Configuration) : Fin 3 → ℂ × ℂ :=
  ![(Q.vertex 0 1 (by decide), Q.vertex 2 3 (by decide)),
    (Q.vertex 0 2 (by decide), Q.vertex 1 3 (by decide)),
    (Q.vertex 0 3 (by decide), Q.vertex 1 2 (by decide))]

/-- The standard midpoint of each of the three diagonal segments. -/
noncomputable def diagonalMidpoint (Q : Configuration) (d : Fin 3) : ℂ :=
  midpoint ℝ (Q.diagonalEndpoints d).1 (Q.diagonalEndpoints d).2

/-- OWN DEFINITION: triangle i uses exactly the three lines other than i. -/
noncomputable def triangleVertices (Q : Configuration) : Fin 4 → Fin 3 → ℂ :=
  ![![Q.vertex 1 2 (by decide), Q.vertex 1 3 (by decide), Q.vertex 2 3 (by decide)],
    ![Q.vertex 0 2 (by decide), Q.vertex 0 3 (by decide), Q.vertex 2 3 (by decide)],
    ![Q.vertex 0 1 (by decide), Q.vertex 0 3 (by decide), Q.vertex 1 3 (by decide)],
    ![Q.vertex 0 1 (by decide), Q.vertex 0 2 (by decide), Q.vertex 1 2 (by decide)]]

/-- (comparer bridge) The classical vertex is the repository `meet`. -/
lemma vertex_eq (Q : Configuration) (i j : Fin 4) (hij : i ≠ j) :
    Q.vertex i j hij = QuadNewton.meet (Q.rl i) (Q.rl j) := by
  have h := Classical.choose_spec (Q.vertex_exists_unique i j hij)
  exact (QuadNewton.meet_eq_iff (Q.rl_cr_ne hij) _).1 ⟨(Q.mem_rl i _).2 h.1.1, (Q.mem_rl j _).2 h.1.2⟩

lemma tv0 (Q : Configuration) : Q.triangleVertices 0 =
    ![QuadNewton.meet (Q.rl 1) (Q.rl 2), QuadNewton.meet (Q.rl 1) (Q.rl 3),
      QuadNewton.meet (Q.rl 2) (Q.rl 3)] := by simp [triangleVertices, vertex_eq]
lemma tv1 (Q : Configuration) : Q.triangleVertices 1 =
    ![QuadNewton.meet (Q.rl 0) (Q.rl 2), QuadNewton.meet (Q.rl 0) (Q.rl 3),
      QuadNewton.meet (Q.rl 2) (Q.rl 3)] := by simp [triangleVertices, vertex_eq]
lemma tv2 (Q : Configuration) : Q.triangleVertices 2 =
    ![QuadNewton.meet (Q.rl 0) (Q.rl 1), QuadNewton.meet (Q.rl 0) (Q.rl 3),
      QuadNewton.meet (Q.rl 1) (Q.rl 3)] := by simp [triangleVertices, vertex_eq]
lemma tv3 (Q : Configuration) : Q.triangleVertices 3 =
    ![QuadNewton.meet (Q.rl 0) (Q.rl 1), QuadNewton.meet (Q.rl 0) (Q.rl 2),
      QuadNewton.meet (Q.rl 1) (Q.rl 2)] := by simp [triangleVertices, vertex_eq]

/-- CONSTRUCTION OBLIGATION: no three configuration lines are concurrent, so
these triples are affinely independent. This is not an added hypothesis. -/
theorem triangle_independent (Q : Configuration) (i : Fin 4) :
    AffineIndependent ℝ (Q.triangleVertices i) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := QuadNewton.genPos_triangles Q.genPos
  fin_cases i
  · rw [show ((⟨0, by decide⟩ : Fin 4)) = 0 from rfl, tv0]; exact affineIndependent_iff_not_collinear_set.2 t1
  · rw [show ((⟨1, by decide⟩ : Fin 4)) = 1 from rfl, tv1]; exact affineIndependent_iff_not_collinear_set.2 t2
  · rw [show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, tv2]; exact affineIndependent_iff_not_collinear_set.2 t3
  · rw [show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, tv3]; exact affineIndependent_iff_not_collinear_set.2 t4

/-- Mathlib's genuine nondegenerate triangle. -/
noncomputable def triangle (Q : Configuration) (i : Fin 4) : Affine.Triangle ℝ ℂ :=
  ⟨Q.triangleVertices i, Q.triangle_independent i⟩

/-- Mathlib's orthocenter, with no substitute coordinate definition. -/
noncomputable def orthocenter (Q : Configuration) (i : Fin 4) : ℂ :=
  Affine.Triangle.orthocenter (Q.triangle i)

/-- Mathlib's circumcircle (a sphere in the two-dimensional real plane). -/
noncomputable def circumcircle (Q : Configuration) (i : Fin 4) :
    EuclideanGeometry.Sphere ℂ :=
  Affine.Simplex.circumsphere (Q.triangle i)

noncomputable def circumcenter (Q : Configuration) (i : Fin 4) : ℂ :=
  (Q.circumcircle i).center

/-- OWN DEFINITION: the circle with the diagonal as diameter. Its center is the
Mathlib midpoint and its radius is half the distance between its endpoints. -/
noncomputable def diameterCircle (Q : Configuration) (d : Fin 3) :
    EuclideanGeometry.Sphere ℂ :=
  { center := Q.diagonalMidpoint d
    radius := dist (Q.diagonalEndpoints d).1 (Q.diagonalEndpoints d).2 / 2 }

/-- OWN DEFINITION: a Miquel point means a point on all four circumcircles.
There is deliberately no formula or arbitrary preselected Miquel point. -/
def IsMiquelPoint (Q : Configuration) (M : ℂ) : Prop :=
  ∀ i : Fin 4, M ∈ Q.circumcircle i

/-- Perpendicular foot, using Mathlib's Euclidean orthogonal projection. -/
noncomputable def foot (Q : Configuration) (M : ℂ) (i : Fin 4) : ℂ :=
  by
    letI : Nonempty (Q.carrier i) := by
      unfold carrier
      infer_instance
    exact (EuclideanGeometry.orthogonalProjection (Q.carrier i) M).val

end Configuration

/-- OWN DEFINITION: signed power of a point with respect to a circle. -/
noncomputable def power (C : EuclideanGeometry.Sphere ℂ) (p : ℂ) : ℝ :=
  dist p C.center ^ 2 - C.radius ^ 2

/-- OWN DEFINITION: the radical locus is exactly the set of equal-power points.
It is not assumed to be a line as part of this definition. -/
def radicalLocus (C D : EuclideanGeometry.Sphere ℂ) : Set ℂ :=
  {p | power C p = power D p}

/-- OWN DEFINITION: affine lines are perpendicular when all their direction
vectors have zero real inner product. IsLine is separately required at uses. -/
def Perpendicular (s t : AffineSubspace ℝ ℂ) : Prop :=
  ∀ u ∈ s.direction, ∀ v ∈ t.direction, inner ℝ u v = 0

/-! ## L15 comparison theorems (comparer-written; statements of `cov_*` copied from `classical_*`) -/

lemma range3 {α : Type*} (f : Fin 3 → α) : Set.range f = {f 0, f 1, f 2} := by
  ext x; constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

lemma range4 {α : Type*} (f : Fin 4 → α) : Set.range f = {f 0, f 1, f 2, f 3} := by
  ext x; constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

lemma mid_eq (a b : ℂ) : midpoint ℝ a b = (a + b) / 2 := by
  rw [midpoint_eq_smul_add, Complex.real_smul]; simp only [invOf_eq_inv]; push_cast; ring

/-- Elementary (comparer, NEW): perpendicularity/cross-product duality in the plane. -/
lemma cross_iff_dot {a1 a2 b1 b2 w1 w2 : ℝ} (hw : w1 ≠ 0 ∨ w2 ≠ 0) (ha : a1 ≠ 0 ∨ a2 ≠ 0)
    (haw : a1 * w1 + a2 * w2 = 0) : a1 * b2 - a2 * b1 = 0 ↔ b1 * w1 + b2 * w2 = 0 := by
  constructor
  · intro h
    rcases ha with ha | ha
    · have : a1 * (b1 * w1 + b2 * w2) = 0 := by linear_combination w2 * h + b1 * haw
      exact (mul_eq_zero.1 this).resolve_left ha
    · have : a2 * (b1 * w1 + b2 * w2) = 0 := by linear_combination (-w1) * h + b2 * haw
      exact (mul_eq_zero.1 this).resolve_left ha
  · intro h
    rcases hw with hw | hw
    · have : w1 * (a1 * b2 - a2 * b1) = 0 := by linear_combination (-a2) * h + b2 * haw
      exact (mul_eq_zero.1 this).resolve_left hw
    · have : w2 * (a1 * b2 - a2 * b1) = 0 := by linear_combination a1 * h - b1 * haw
      exact (mul_eq_zero.1 this).resolve_left hw

lemma ne_re_im {z w : ℂ} (h : z ≠ w) : w.re - z.re ≠ 0 ∨ w.im - z.im ≠ 0 := by
  by_contra hc; push Not at hc
  exact h (Complex.ext (by linarith [hc.1]) (by linarith [hc.2]))

/-- (comparer, NEW) The radical locus of two circles with distinct centres containing two distinct
points `H ≠ H'` is exactly the line `H H'`. -/
lemma radical_eq_line (C D : EuclideanGeometry.Sphere ℂ) (hc : C.center ≠ D.center) {H H' : ℂ}
    (hH : H ∈ radicalLocus C D) (hH' : H' ∈ radicalLocus C D) (hne : H ≠ H') :
    radicalLocus C D = (line[ℝ, H, H'] : Set ℂ) := by
  have hl : (line[ℝ, H, H'] : Set ℂ) = (⟨H, H' - H⟩ : QuadNewton.Line).carrier := by
    rw [QuadNewton.carrier_eq_line _ (sub_ne_zero.2 hne.symm)]; simp
  rw [hl]; ext z
  simp only [radicalLocus, power, Set.mem_ofPred_eq, QuadNewton.Line.carrier, QuadNewton.cr_def,
    Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hH hH' ⊢
  have i2 : (H'.re - H.re) * (D.center.re - C.center.re) + (H'.im - H.im) * (D.center.im - C.center.im) = 0 := by
    linear_combination (1/2 : ℝ) * (hH' - hH)
  rw [cross_iff_dot (ne_re_im hc) (ne_re_im hne) i2]
  constructor
  · intro h; linear_combination (1/2 : ℝ) * (h - hH)
  · intro h; linear_combination hH + 2 * h

namespace Configuration

lemma triangle_eq (Q : Configuration) (i : Fin 4) {a b c : ℂ} (h : Q.triangleVertices i = ![a, b, c])
    (hc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    Q.triangle i = ⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 hc⟩ := by
  unfold triangle; congr 1

lemma orthocenter_eq (Q : Configuration) (i : Fin 4) {a b c : ℂ} (h : Q.triangleVertices i = ![a, b, c])
    (hc : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : Q.orthocenter i = QuadNewton.ortho a b c := by
  rw [QuadNewton.ortho_eq_orthocenter hc, orthocenter, Q.triangle_eq i h hc]

lemma H_eq (Q : Configuration) :
    Q.orthocenter 0 = QuadNewton.ortho (QuadNewton.meet (Q.rl 1) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)) ∧
    Q.orthocenter 1 = QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)) ∧
    Q.orthocenter 2 = QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)) ∧
    Q.orthocenter 3 = QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 2)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := QuadNewton.genPos_triangles Q.genPos
  exact ⟨Q.orthocenter_eq 0 Q.tv0 t1, Q.orthocenter_eq 1 Q.tv1 t2, Q.orthocenter_eq 2 Q.tv2 t3,
    Q.orthocenter_eq 3 Q.tv3 t4⟩

lemma range_H (Q : Configuration) : Set.range Q.orthocenter =
    {QuadNewton.ortho (QuadNewton.meet (Q.rl 1) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 2))} := by
  obtain ⟨e0, e1, e2, e3⟩ := Q.H_eq
  rw [range4, e0, e1, e2, e3]

lemma H_mem (Q : Configuration) (i : Fin 4) : Q.orthocenter i ∈
    ({QuadNewton.ortho (QuadNewton.meet (Q.rl 1) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 2) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 3)) (QuadNewton.meet (Q.rl 1) (Q.rl 3)),
     QuadNewton.ortho (QuadNewton.meet (Q.rl 0) (Q.rl 1)) (QuadNewton.meet (Q.rl 0) (Q.rl 2)) (QuadNewton.meet (Q.rl 1) (Q.rl 2))} : Set ℂ) := by
  rw [← Q.range_H]; exact Set.mem_range_self i

lemma de_eq (Q : Configuration) :
    Q.diagonalEndpoints 0 = (QuadNewton.meet (Q.rl 0) (Q.rl 1), QuadNewton.meet (Q.rl 2) (Q.rl 3)) ∧
    Q.diagonalEndpoints 1 = (QuadNewton.meet (Q.rl 0) (Q.rl 2), QuadNewton.meet (Q.rl 1) (Q.rl 3)) ∧
    Q.diagonalEndpoints 2 = (QuadNewton.meet (Q.rl 0) (Q.rl 3), QuadNewton.meet (Q.rl 1) (Q.rl 2)) := by
  simp [diagonalEndpoints, vertex_eq]

lemma dm_eq (Q : Configuration) (d : Fin 3) :
    Q.diagonalMidpoint d = ((Q.diagonalEndpoints d).1 + (Q.diagonalEndpoints d).2) / 2 := mid_eq _ _

lemma range_dm (Q : Configuration) : Set.range Q.diagonalMidpoint =
    {(QuadNewton.meet (Q.rl 0) (Q.rl 1) + QuadNewton.meet (Q.rl 2) (Q.rl 3)) / 2,
     (QuadNewton.meet (Q.rl 0) (Q.rl 2) + QuadNewton.meet (Q.rl 1) (Q.rl 3)) / 2,
     (QuadNewton.meet (Q.rl 0) (Q.rl 3) + QuadNewton.meet (Q.rl 1) (Q.rl 2)) / 2} := by
  obtain ⟨e0, e1, e2⟩ := Q.de_eq
  rw [range3, dm_eq, dm_eq, dm_eq, e0, e1, e2]

lemma power_diam (Q : Configuration) (d : Fin 3) (z : ℂ) :
    power (Q.diameterCircle d) z = QuadNewton.pw z (Q.diagonalEndpoints d).1 (Q.diagonalEndpoints d).2 := by
  simp only [power, diameterCircle, dm_eq, QuadNewton.pw, Complex.dist_eq]; ring

lemma dm_ne (Q : Configuration) {d e : Fin 3} (hde : d ≠ e) : Q.diagonalMidpoint d ≠ Q.diagonalMidpoint e := by
  obtain ⟨-, n01, n02, n12⟩ := QuadNewton.bodenmiller_coaxal Q.genPos
  simp only [QuadNewton.diamCircle] at n01 n02 n12
  obtain ⟨e0, e1, e2⟩ := Q.de_eq
  have m0 := Q.dm_eq 0
  have m1 := Q.dm_eq 1
  have m2 := Q.dm_eq 2
  rw [e0] at m0; rw [e1] at m1; rw [e2] at m2
  have k01 : Q.diagonalMidpoint 0 ≠ Q.diagonalMidpoint 1 := by rw [m0, m1]; exact n01
  have k02 : Q.diagonalMidpoint 0 ≠ Q.diagonalMidpoint 2 := by rw [m0, m2]; exact n02
  have k12 : Q.diagonalMidpoint 1 ≠ Q.diagonalMidpoint 2 := by rw [m1, m2]; exact n12
  fin_cases d <;> fin_cases e <;> first
    | exact absurd rfl hde | exact k01 | exact k02 | exact k12
    | exact k01.symm | exact k02.symm | exact k12.symm

lemma exists_H_ne (Q : Configuration) : ∃ i j : Fin 4, Q.orthocenter i ≠ Q.orthocenter j := by
  obtain ⟨e0, e1, e2, e3⟩ := Q.H_eq
  rcases QuadNewton.orthocentres_not_all_eq Q.genPos with h | h
  · exact ⟨2, 3, by rw [e2, e3]; exact h⟩
  · exact ⟨1, 3, by rw [e1, e3]; exact h⟩

end Configuration

open QuadNewton.Classical.Configuration

/-- E1(a), Newton--Gauss: the three diagonal midpoints are collinear. -/
theorem cov_E1_a (Q : Configuration) :
    Collinear ℝ (Set.range Q.diagonalMidpoint) := by
  rw [Q.range_dm]; exact QuadNewton.newton_gauss Q.genPos

/-- E1(b): the Newton--Gauss line does not collapse to a single point. -/
theorem cov_E1_b (Q : Configuration) :
    ∃ d e : Fin 3, Q.diagonalMidpoint d ≠ Q.diagonalMidpoint e := by
  refine ⟨0, 1, ?_⟩
  obtain ⟨e0, e1, -⟩ := Q.de_eq
  rw [dm_eq, dm_eq, e0, e1]; exact QuadNewton.diag_midpoints_ne Q.genPos

/-- E2(a), Steiner/Bodenmiller: the four orthocentres are collinear. -/
theorem cov_E2_a (Q : Configuration) :
    Collinear ℝ (Set.range Q.orthocenter) := by
  rw [Q.range_H]; exact QuadNewton.orthocentres_collinear Q.genPos

/-- E2(b): the orthocentres are not all the same point. -/
theorem cov_E2_b (Q : Configuration) :
    ∃ i j : Fin 4, Q.orthocenter i ≠ Q.orthocenter j := Q.exists_H_ne

/-- E3(a), Gauss--Bodenmiller: each orthocentre has equal power with respect
to all three diameter circles. This spells out the stated meaning of coaxality. -/
theorem cov_E3_a (Q : Configuration) :
    ∀ (i : Fin 4) (d e : Fin 3),
      power (Q.diameterCircle d) (Q.orthocenter i) =
        power (Q.diameterCircle e) (Q.orthocenter i) := by
  have key : ∀ (i : Fin 4) (d : Fin 3),
      power (Q.diameterCircle d) (Q.orthocenter i) = power (Q.diameterCircle 0) (Q.orthocenter i) := by
    intro i d
    obtain ⟨b1, b2⟩ := QuadNewton.bodenmiller Q.genPos _ (Q.H_mem i)
    obtain ⟨e0, e1, e2⟩ := Q.de_eq
    fin_cases d
    · rfl
    · simp only [Fin.mk_one]; rw [power_diam, power_diam, e0, e1]; exact b1.symm
    · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, power_diam, power_diam, e0, e2]; exact b2.symm
  intro i d e; rw [key i d, key i e]

/-- E3(b): a genuine line contains all the orthocentres and is the exact
radical locus of every pair of distinct diagonal circles. -/
theorem cov_E3_b (Q : Configuration) :
    ∃ a : AffineSubspace ℝ ℂ, IsLine a ∧
      (∀ i : Fin 4, Q.orthocenter i ∈ a) ∧
      ∀ d e : Fin 3, d ≠ e →
        radicalLocus (Q.diameterCircle d) (Q.diameterCircle e) = (a : Set ℂ) := by
  obtain ⟨i, j, hij⟩ := Q.exists_H_ne
  refine ⟨line[ℝ, Q.orthocenter i, Q.orthocenter j], ⟨_, _, hij, rfl⟩, fun k => ?_, fun d e hde => ?_⟩
  · exact (cov_E2_a Q).mem_affineSpan_of_mem_of_ne (Set.mem_range_self i) (Set.mem_range_self j)
      (Set.mem_range_self k) hij
  · exact radical_eq_line _ _ (Q.dm_ne hde) (cov_E3_a Q i d e) (cov_E3_a Q j d e) hij

/-- E4: there are genuine Newton--Gauss and orthocentre lines, and they are
perpendicular. E1(b) and E2(b) ensure that the indicated carriers are unique;
no existence of carriers is imposed as an additional hypothesis. -/
theorem cov_E4_a (Q : Configuration) :
    ∃ n o : AffineSubspace ℝ ℂ, IsLine n ∧ IsLine o ∧
      (∀ d : Fin 3, Q.diagonalMidpoint d ∈ n) ∧
      (∀ i : Fin 4, Q.orthocenter i ∈ o) ∧
      Perpendicular n o := by
  obtain ⟨i, j, hij⟩ := Q.exists_H_ne
  have h01 : Q.diagonalMidpoint 0 ≠ Q.diagonalMidpoint 1 := Q.dm_ne (by decide)
  refine ⟨line[ℝ, Q.diagonalMidpoint 0, Q.diagonalMidpoint 1], line[ℝ, Q.orthocenter i, Q.orthocenter j],
    ⟨_, _, h01, rfl⟩, ⟨_, _, hij, rfl⟩, fun d => ?_, fun k => ?_, ?_⟩
  · exact (cov_E1_a Q).mem_affineSpan_of_mem_of_ne (Set.mem_range_self 0) (Set.mem_range_self 1)
      (Set.mem_range_self d) h01
  · exact (cov_E2_a Q).mem_affineSpan_of_mem_of_ne (Set.mem_range_self i) (Set.mem_range_self j)
      (Set.mem_range_self k) hij
  · intro u hu v hv
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton] at hu hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    have hp := QuadNewton.orthocentre_line_perp_inner Q.genPos _ (Q.H_mem j) _ (Q.H_mem i)
    obtain ⟨e0, e1, -⟩ := Q.de_eq
    rw [real_inner_smul_left, real_inner_smul_right, vsub_eq_sub, vsub_eq_sub, dm_eq, dm_eq, e0, e1,
      show (QuadNewton.meet (Q.rl 0) (Q.rl 1) + QuadNewton.meet (Q.rl 2) (Q.rl 3)) / 2 -
        (QuadNewton.meet (Q.rl 0) (Q.rl 2) + QuadNewton.meet (Q.rl 1) (Q.rl 3)) / 2 =
        -((QuadNewton.meet (Q.rl 0) (Q.rl 2) + QuadNewton.meet (Q.rl 1) (Q.rl 3)) / 2 -
        (QuadNewton.meet (Q.rl 0) (Q.rl 1) + QuadNewton.meet (Q.rl 2) (Q.rl 3)) / 2) by ring,
      inner_neg_left, hp, neg_zero, mul_zero, mul_zero]


end

end QuadNewton.Classical
