import QuadNewton.Bridge

/-!
# Layer 14: Mathlib-only restatements of the Newton–Gauss / orthocentre side

Every `l14_*` theorem below has a statement mentioning only Mathlib notions. The four lines are
`line[ℝ, pᵢ, qᵢ]` with `pᵢ ≠ qᵢ`; general position is stated with `AffineSubspace.Parallel` and
common points; the six vertices are any points `aᵢⱼ` lying on both lines; the four triangles are
Mathlib triangles with the given vertices; orthocentres are `Affine.Triangle.orthocenter`,
midpoints are `midpoint ℝ`, the circles on the diagonals are `EuclideanGeometry.Sphere`s with
centre the midpoint and radius half the length, and power is `EuclideanGeometry.Sphere.power`.
The `l14b_*` lemmas are the bridges to the library's own definitions; the `l14w_*` theorems are
explicit witnesses (non-vacuity).
-/

open Complex ComplexConjugate

namespace QuadNewton

/-! ### Bridges -/

theorem l14b_mem {p q z : ℂ} (h : p ≠ q) : z ∈ (⟨p, q - p⟩ : Line).carrier ↔ z ∈ line[ℝ, p, q] := by
  rw [carrier_eq_line _ (sub_ne_zero.2 h.symm)]; simp

theorem l14b_mem_iff {p q z : ℂ} (h : p ≠ q) : z ∈ line[ℝ, p, q] ↔ cr (q - p) (z - p) = 0 := by
  rw [← l14b_mem h]; rfl

theorem l14b_genPos {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℂ}
    (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
    (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
    (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
    (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
    (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
    (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
    (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
    (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
    (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄]) :
    GenPos ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
  rw [genPos_iff]
  simp only [Line.toAffine, add_sub_cancel]
  exact ⟨⟨sub_ne_zero.2 h₁.symm, sub_ne_zero.2 h₂.symm, sub_ne_zero.2 h₃.symm,
    sub_ne_zero.2 h₄.symm⟩, ⟨n₁₂, n₁₃, n₁₄, n₂₃, n₂₄, n₃₄⟩, c₁₂₃, c₁₂₄, c₁₃₄, c₂₃₄⟩

theorem l14b_meet {p q p' q' a : ℂ} (h : p ≠ q) (h' : p' ≠ q')
    (hc : cr (⟨p, q - p⟩ : Line).d (⟨p', q' - p'⟩ : Line).d ≠ 0)
    (ha : a ∈ line[ℝ, p, q] ∧ a ∈ line[ℝ, p', q']) : a = meet ⟨p, q - p⟩ ⟨p', q' - p'⟩ :=
  (meet_eq_iff (by rw [cr_comm]; exact neg_ne_zero.2 hc) a).1
    ⟨(l14b_mem h).2 ha.1, (l14b_mem h').2 ha.2⟩

theorem l14b_setup {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : ℂ}
    (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
    (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
    (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
    (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
    (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
    (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
    (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
    (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
    (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
    (m₁₂ : a₁₂ ∈ line[ℝ, p₁, q₁] ∧ a₁₂ ∈ line[ℝ, p₂, q₂])
    (m₁₃ : a₁₃ ∈ line[ℝ, p₁, q₁] ∧ a₁₃ ∈ line[ℝ, p₃, q₃])
    (m₁₄ : a₁₄ ∈ line[ℝ, p₁, q₁] ∧ a₁₄ ∈ line[ℝ, p₄, q₄])
    (m₂₃ : a₂₃ ∈ line[ℝ, p₂, q₂] ∧ a₂₃ ∈ line[ℝ, p₃, q₃])
    (m₂₄ : a₂₄ ∈ line[ℝ, p₂, q₂] ∧ a₂₄ ∈ line[ℝ, p₄, q₄])
    (m₃₄ : a₃₄ ∈ line[ℝ, p₃, q₃] ∧ a₃₄ ∈ line[ℝ, p₄, q₄]) :
    GenPos ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ ∧
    a₁₂ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₂, q₂ - p₂⟩ ∧ a₁₃ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₁₄ = meet ⟨p₁, q₁ - p₁⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₂₃ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₃, q₃ - p₃⟩ ∧
    a₂₄ = meet ⟨p₂, q₂ - p₂⟩ ⟨p₄, q₄ - p₄⟩ ∧ a₃₄ = meet ⟨p₃, q₃ - p₃⟩ ⟨p₄, q₄ - p₄⟩ := by
  have hG := l14b_genPos h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄
  exact ⟨hG, l14b_meet h₁ h₂ hG.p12 m₁₂, l14b_meet h₁ h₃ hG.p13 m₁₃, l14b_meet h₁ h₄ hG.p14 m₁₄,
    l14b_meet h₂ h₃ hG.p23 m₂₃, l14b_meet h₂ h₄ hG.p24 m₂₄, l14b_meet h₃ h₄ hG.p34 m₃₄⟩

theorem l14b_tri {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    T = ⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 hn⟩ :=
  Affine.Simplex.ext fun i => by rw [e]

theorem l14b_orthocenter {T : Affine.Triangle ℝ ℂ} {a b c : ℂ} (e : T.points = ![a, b, c])
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : T.orthocenter = ortho a b c := by
  rw [ortho_eq_orthocenter hn, ← l14b_tri e hn]

theorem l14b_midpoint (x y : ℂ) : midpoint ℝ x y = (x + y) / 2 := by
  rw [midpoint_eq_smul_add ℝ x y, invOf_eq_inv, Complex.real_smul]; push_cast; ring

theorem l14b_sphere (P Q : ℂ) :
    (⟨midpoint ℝ P Q, dist P Q / 2⟩ : EuclideanGeometry.Sphere ℂ) = diamCircle P Q := by
  rw [diamCircle, l14b_midpoint]

theorem l14b_setupT {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄)
    {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![meet L₂ L₃, meet L₂ L₄, meet L₃ L₄])
    (e₂ : T₂.points = ![meet L₁ L₃, meet L₁ L₄, meet L₃ L₄])
    (e₃ : T₃.points = ![meet L₁ L₂, meet L₁ L₄, meet L₂ L₄])
    (e₄ : T₄.points = ![meet L₁ L₂, meet L₁ L₃, meet L₂ L₃]) :
    T₁.orthocenter = ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) ∧
    T₂.orthocenter = ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ∧
    T₃.orthocenter = ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ∧
    T₄.orthocenter = ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := genPos_triangles h
  exact ⟨l14b_orthocenter e₁ t1, l14b_orthocenter e₂ t2, l14b_orthocenter e₃ t3,
    l14b_orthocenter e₄ t4⟩

theorem l14b_parallel_iff {p q p' q' : ℂ} (h : p ≠ q) (h' : p' ≠ q') :
    line[ℝ, p, q].Parallel line[ℝ, p', q'] ↔ cr (q - p) (q' - p') = 0 := by
  have := parallel_iff_cr (L := ⟨p, q - p⟩) (M := ⟨p', q' - p'⟩) (sub_ne_zero.2 h.symm)
    (sub_ne_zero.2 h'.symm)
  simpa [Line.toAffine] using this

theorem l14b_noconc {p q p' q' p'' q'' a : ℂ} (h : p ≠ q) (h' : p' ≠ q') (h'' : p'' ≠ q'')
    (hc : cr (q - p) (q' - p') ≠ 0) (ha : a ∈ line[ℝ, p, q] ∧ a ∈ line[ℝ, p', q'])
    (hn : cr (q'' - p'') (a - p'') ≠ 0) :
    ¬ ∃ z, z ∈ line[ℝ, p, q] ∧ z ∈ line[ℝ, p', q'] ∧ z ∈ line[ℝ, p'', q''] := by
  rintro ⟨z, hz, hz', hz''⟩
  have e1 := l14b_meet h h' hc ha
  have e2 := l14b_meet h h' hc ⟨hz, hz'⟩
  rw [l14b_mem_iff h'', e2, ← e1] at hz''
  exact hn hz''

/-! ### The Mathlib-only statements -/

section Config

variable {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℂ}
  (h₁ : p₁ ≠ q₁) (h₂ : p₂ ≠ q₂) (h₃ : p₃ ≠ q₃) (h₄ : p₄ ≠ q₄)
  (n₁₂ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₂, q₂])
  (n₁₃ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₃, q₃])
  (n₁₄ : ¬ line[ℝ, p₁, q₁].Parallel line[ℝ, p₄, q₄])
  (n₂₃ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₃, q₃])
  (n₂₄ : ¬ line[ℝ, p₂, q₂].Parallel line[ℝ, p₄, q₄])
  (n₃₄ : ¬ line[ℝ, p₃, q₃].Parallel line[ℝ, p₄, q₄])
  (c₁₂₃ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃])
  (c₁₂₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₄, q₄])
  (c₁₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₁, q₁] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
  (c₂₃₄ : ¬ ∃ z, z ∈ line[ℝ, p₂, q₂] ∧ z ∈ line[ℝ, p₃, q₃] ∧ z ∈ line[ℝ, p₄, q₄])
  {a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : ℂ}
  (m₁₂ : a₁₂ ∈ line[ℝ, p₁, q₁] ∧ a₁₂ ∈ line[ℝ, p₂, q₂])
  (m₁₃ : a₁₃ ∈ line[ℝ, p₁, q₁] ∧ a₁₃ ∈ line[ℝ, p₃, q₃])
  (m₁₄ : a₁₄ ∈ line[ℝ, p₁, q₁] ∧ a₁₄ ∈ line[ℝ, p₄, q₄])
  (m₂₃ : a₂₃ ∈ line[ℝ, p₂, q₂] ∧ a₂₃ ∈ line[ℝ, p₃, q₃])
  (m₂₄ : a₂₄ ∈ line[ℝ, p₂, q₂] ∧ a₂₄ ∈ line[ℝ, p₄, q₄])
  (m₃₄ : a₃₄ ∈ line[ℝ, p₃, q₃] ∧ a₃₄ ∈ line[ℝ, p₄, q₄])
include h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄ c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄

/-- The four triangles exist as Mathlib triangles (their vertices are affinely independent). -/
theorem l14_triangles_exist :
    ∃ T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ, T₁.points = ![a₂₃, a₂₄, a₃₄] ∧
      T₂.points = ![a₁₃, a₁₄, a₃₄] ∧ T₃.points = ![a₁₂, a₁₄, a₂₄] ∧
      T₄.points = ![a₁₂, a₁₃, a₂₃] := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨t1, t2, t3, t4, -⟩ := genPos_triangles hG
  exact ⟨⟨_, affineIndependent_iff_not_collinear_set.2 t1⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t2⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t3⟩,
    ⟨_, affineIndependent_iff_not_collinear_set.2 t4⟩, rfl, rfl, rfl, rfl⟩

/-- **Newton–Gauss line**, Mathlib form: the midpoints of the three diagonals are collinear. -/
theorem l14_newton_gauss :
    Collinear ℝ ({midpoint ℝ a₁₂ a₃₄, midpoint ℝ a₁₃ a₂₄, midpoint ℝ a₁₄ a₂₃} : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  simp only [l14b_midpoint]
  exact newton_gauss hG

/-- The three diagonal midpoints are pairwise distinct (so the Newton–Gauss line is determined). -/
theorem l14_diag_midpoints_ne :
    midpoint ℝ a₁₂ a₃₄ ≠ midpoint ℝ a₁₃ a₂₄ ∧ midpoint ℝ a₁₂ a₃₄ ≠ midpoint ℝ a₁₄ a₂₃ ∧
      midpoint ℝ a₁₃ a₂₄ ≠ midpoint ℝ a₁₄ a₂₃ := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨-, d1, d2, d3⟩ := bodenmiller_coaxal hG
  simp only [diamCircle] at d1 d2 d3
  simp only [l14b_midpoint]
  exact ⟨d1, d2, d3⟩

/-- **Orthocentre line**, Mathlib form: the four orthocentres are collinear. -/
theorem l14_orthocentres_collinear {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    Collinear ℝ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ) := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₁, o₂, o₃, o₄]
  exact orthocentres_collinear hG

/-- The four orthocentres are not all equal. -/
theorem l14_orthocentres_not_all_eq {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    T₃.orthocenter ≠ T₄.orthocenter ∨ T₂.orthocenter ≠ T₄.orthocenter := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨-, o₂, o₃, o₄⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₂, o₃, o₄]
  exact orthocentres_not_all_eq hG

/-- **Gauss–Bodenmiller**, Mathlib form: each orthocentre has equal power
(`EuclideanGeometry.Sphere.power`) w.r.t. the three circles on the diagonals as diameters. -/
theorem l14_bodenmiller {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    ∀ H ∈ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ),
      (⟨midpoint ℝ a₁₂ a₃₄, dist a₁₂ a₃₄ / 2⟩ : EuclideanGeometry.Sphere ℂ).power H =
          (⟨midpoint ℝ a₁₃ a₂₄, dist a₁₃ a₂₄ / 2⟩ : EuclideanGeometry.Sphere ℂ).power H ∧
        (⟨midpoint ℝ a₁₂ a₃₄, dist a₁₂ a₃₄ / 2⟩ : EuclideanGeometry.Sphere ℂ).power H =
          (⟨midpoint ℝ a₁₄ a₂₃, dist a₁₄ a₂₃ / 2⟩ : EuclideanGeometry.Sphere ℂ).power H := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₁, o₂, o₃, o₄]
  simp only [l14b_sphere]
  exact (bodenmiller_coaxal hG).1

/-- **Orthocentre line ⟂ Newton–Gauss line**, Mathlib form (real inner product on `ℂ`). -/
theorem l14_orthocentre_line_perp {T₁ T₂ T₃ T₄ : Affine.Triangle ℝ ℂ}
    (e₁ : T₁.points = ![a₂₃, a₂₄, a₃₄]) (e₂ : T₂.points = ![a₁₃, a₁₄, a₃₄])
    (e₃ : T₃.points = ![a₁₂, a₁₄, a₂₄]) (e₄ : T₄.points = ![a₁₂, a₁₃, a₂₃]) :
    ∀ H₁ ∈ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ),
    ∀ H₂ ∈ ({T₁.orthocenter, T₂.orthocenter, T₃.orthocenter, T₄.orthocenter} : Set ℂ),
      inner ℝ (midpoint ℝ a₁₃ a₂₄ - midpoint ℝ a₁₂ a₃₄) (H₂ - H₁) = 0 := by
  obtain ⟨hG, rfl, rfl, rfl, rfl, rfl, rfl⟩ := l14b_setup h₁ h₂ h₃ h₄ n₁₂ n₁₃ n₁₄ n₂₃ n₂₄ n₃₄
    c₁₂₃ c₁₂₄ c₁₃₄ c₂₃₄ m₁₂ m₁₃ m₁₄ m₂₃ m₂₄ m₃₄
  obtain ⟨o₁, o₂, o₃, o₄⟩ := l14b_setupT hG e₁ e₂ e₃ e₄
  rw [o₁, o₂, o₃, o₄]
  simp only [l14b_midpoint]
  exact orthocentre_line_perp_inner hG

end Config

/-! ### Witnesses (non-vacuity) -/

theorem l14wbA_base :
    (0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) := by
  have h1 : (0 : ℂ) ≠ 1 := by norm_num [Complex.ext_iff]
  have h2 : (1 - I : ℂ) ≠ -2 + 2 * I := by norm_num [Complex.ext_iff]
  have h3 : (-1 + 3 * I : ℂ) ≠ -2 := by norm_num [Complex.ext_iff]
  have h4 : (-1 - 2 * I : ℂ) ≠ 3 := by norm_num [Complex.ext_iff]
  have m12 : (0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h2]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m13 : (-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m14 : (3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m23 : (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m24 : (1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m34 : (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3] := by
    rw [l14b_mem_iff h3, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨h1, h2, h3, h4,
    (by rw [l14b_parallel_iff h1 h2]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h1 h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h1 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h2 h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h2 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h3 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (l14b_noconc h1 h2 h3 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h1 h2 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h1 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m13 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h2 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m23 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    m12, m13, m14, m23, m24, m34⟩

theorem l14wbA_master :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧
    T1.orthocenter = -1/2 - 1/2 * I ∧
    T2.orthocenter = -3 + 2 * I ∧
    T3.orthocenter = 1 - 2 * I ∧
    T4.orthocenter = -3/2 + 1/2 * I := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbA_base
  obtain ⟨T1, T2, T3, T4, e1, e2, e3, e4⟩ := l14_triangles_exist h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  have o1 : T1.orthocenter = -1/2 - 1/2 * I := by
    rw [l14b_orthocenter e1 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o2 : T2.orthocenter = -3 + 2 * I := by
    rw [l14b_orthocenter e2 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o3 : T3.orthocenter = 1 - 2 * I := by
    rw [l14b_orthocenter e3 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o4 : T4.orthocenter = -3/2 + 1/2 * I := by
    rw [l14b_orthocenter e4 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, o1, o2, o3, o4⟩

/-- Witness for `l14_newton_gauss`: the three diagonal midpoints are pairwise distinct. -/
theorem l14w_newton_gauss :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    midpoint ℝ (0 : ℂ) (-3 - 3 * I) = -3/2 - 3/2 * I ∧
    midpoint ℝ (-2 : ℂ) (1 - I) = -1/2 - 1/2 * I ∧
    midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I) = 3/4 + 3/4 * I ∧
    (-3/2 - 3/2 * I : ℂ) ≠ -1/2 - 1/2 * I ∧
    (-3/2 - 3/2 * I : ℂ) ≠ 3/4 + 3/4 * I ∧
    (-1/2 - 1/2 * I : ℂ) ≠ 3/4 + 3/4 * I := by
  refine ⟨l14wbA_base, ?_⟩
  simp only [l14b_midpoint]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_diag_midpoints_ne` (same configuration; the conclusion is a pure distinctness statement). -/
theorem l14w_diag_midpoints_ne :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    midpoint ℝ (0 : ℂ) (-3 - 3 * I) ≠ midpoint ℝ (-2 : ℂ) (1 - I) ∧ midpoint ℝ (0 : ℂ) (-3 - 3 * I) ≠ midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I) ∧ midpoint ℝ (-2 : ℂ) (1 - I) ≠ midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I) := by
  refine ⟨l14wbA_base, ?_⟩
  simp only [l14b_midpoint]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_orthocentres_collinear`: the orthocentres are explicit and pairwise distinct. -/
theorem l14w_orthocentres_collinear :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧
    T1.orthocenter = -1/2 - 1/2 * I ∧
    T2.orthocenter = -3 + 2 * I ∧
    T3.orthocenter = 1 - 2 * I ∧
    T4.orthocenter = -3/2 + 1/2 * I ∧
    T1.orthocenter ≠ T2.orthocenter ∧
    T1.orthocenter ≠ T3.orthocenter ∧
    T1.orthocenter ≠ T4.orthocenter ∧
    T2.orthocenter ≠ T3.orthocenter ∧
    T2.orthocenter ≠ T4.orthocenter ∧
    T3.orthocenter ≠ T4.orthocenter := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbA_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  refine ⟨o1, o2, o3, o4, ?_⟩
  simp only [o1, o2, o3, o4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_orthocentres_not_all_eq`. -/
theorem l14w_orthocentres_not_all_eq :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧
    (T3.orthocenter ≠ T4.orthocenter ∨ T2.orthocenter ≠ T4.orthocenter) := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbA_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  right
  rw [o2, o4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_bodenmiller`: explicit common powers; the three circles have distinct centres and the orthocentres are distinct. -/
theorem l14w_bodenmiller :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -5/2 ∧
    (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -5/2 ∧
    (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -5/2 ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 10 ∧
    (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 10 ∧
    (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 10 ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 2 ∧
    (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 2 ∧
    (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 2 ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = -1/2 ∧
    (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = -1/2 ∧
    (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = -1/2 ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    (⟨midpoint ℝ (0 : ℂ) (-3 - 3 * I), dist (0 : ℂ) (-3 - 3 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    (⟨midpoint ℝ (-2 : ℂ) (1 - I), dist (-2 : ℂ) (1 - I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (3 : ℂ) (-3/2 + 3/2 * I), dist (3 : ℂ) (-3/2 + 3/2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    T1.orthocenter ≠ T2.orthocenter ∧
    T1.orthocenter ≠ T3.orthocenter ∧
    T1.orthocenter ≠ T4.orthocenter ∧
    T2.orthocenter ≠ T3.orthocenter ∧
    T2.orthocenter ≠ T4.orthocenter ∧
    T3.orthocenter ≠ T4.orthocenter := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbA_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  simp only [o1, o2, o3, o4]
  simp only [EuclideanGeometry.Sphere.power, l14b_midpoint, Complex.dist_eq, div_pow, Complex.sq_norm]
  norm_num [Complex.ext_iff, Complex.normSq_apply]

/-- Witness for `l14_orthocentre_line_perp`: both directions are nonzero (genuine lines). -/
theorem l14w_orthocentre_line_perp :
    ((0 : ℂ) ≠ 1 ∧
    (1 - I : ℂ) ≠ -2 + 2 * I ∧
    (-1 + 3 * I : ℂ) ≠ -2 ∧
    (-1 - 2 * I : ℂ) ≠ 3 ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 + 3 * I : ℂ), -2] ∧
    ¬ line[ℝ, (1 - I : ℂ), -2 + 2 * I].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    ¬ line[ℝ, (-1 + 3 * I : ℂ), -2].Parallel line[ℝ, (-1 - 2 * I : ℂ), 3] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ z ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ z ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I]) ∧
    ((-2 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (-2 : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((3 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (3 : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (-3/2 + 3/2 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2]) ∧
    ((1 - I : ℂ) ∈ line[ℝ, (1 - I : ℂ), -2 + 2 * I] ∧ (1 - I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3]) ∧
    ((-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 + 3 * I : ℂ), -2] ∧ (-3 - 3 * I : ℂ) ∈ line[ℝ, (-1 - 2 * I : ℂ), 3])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-3/2 + 3/2 * I : ℂ), 1 - I, -3 - 3 * I] ∧ T2.points = ![(-2 : ℂ), 3, -3 - 3 * I] ∧ T3.points = ![(0 : ℂ), 3, 1 - I] ∧ T4.points = ![(0 : ℂ), -2, -3/2 + 3/2 * I]) ∧
    midpoint ℝ (-2 : ℂ) (1 - I) - midpoint ℝ (0 : ℂ) (-3 - 3 * I) ≠ 0 ∧ T2.orthocenter - T1.orthocenter ≠ 0 ∧
    inner ℝ (midpoint ℝ (-2 : ℂ) (1 - I) - midpoint ℝ (0 : ℂ) (-3 - 3 * I)) (T2.orthocenter - T1.orthocenter) = 0 := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbA_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  rw [o1, o2]
  simp only [l14b_midpoint, Complex.inner, map_sub, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]
  norm_num [Complex.ext_iff]

theorem l14wbP_base :
    (0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) := by
  have h1 : (0 : ℂ) ≠ 1 := by norm_num [Complex.ext_iff]
  have h2 : (0 : ℂ) ≠ I := by norm_num [Complex.ext_iff]
  have h3 : (-I : ℂ) ≠ -1 - 2 * I := by norm_num [Complex.ext_iff]
  have h4 : (-2 + 3 * I : ℂ) ≠ 2 + I := by norm_num [Complex.ext_iff]
  have m12 : (0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h2]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m13 : (1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m14 : (4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h1, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m23 : (-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m24 : (2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h2, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have m34 : (2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I] := by
    rw [l14b_mem_iff h3, l14b_mem_iff h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨h1, h2, h3, h4,
    (by rw [l14b_parallel_iff h1 h2]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h1 h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h1 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h2 h3]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h2 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (by rw [l14b_parallel_iff h3 h4]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]),
    (l14b_noconc h1 h2 h3 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h1 h2 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m12 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h1 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m13 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    (l14b_noconc h2 h3 h4 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]) m23 (by norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])),
    m12, m13, m14, m23, m24, m34⟩

theorem l14wbP_master :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧
    T1.orthocenter = 1 + I ∧
    T2.orthocenter = 2 + 2 * I ∧
    T3.orthocenter = 0 ∧
    T4.orthocenter = 0 := by
  obtain ⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩ := l14wbP_base
  obtain ⟨T1, T2, T3, T4, e1, e2, e3, e4⟩ := l14_triangles_exist h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 c123 c124 c134 c234 m12 m13 m14 m23 m24 m34
  have o1 : T1.orthocenter = 1 + I := by
    rw [l14b_orthocenter e1 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o2 : T2.orthocenter = 2 + 2 * I := by
    rw [l14b_orthocenter e2 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o3 : T3.orthocenter = 0 := by
    rw [l14b_orthocenter e3 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have o4 : T4.orthocenter = 0 := by
    rw [l14b_orthocenter e4 (by rw [collinear_iff_cr]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im])]; norm_num [Complex.ext_iff, cr, foot, ortho, circ, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨⟨h1, h2, h3, h4, n12, n13, n14, n23, n24, n34, c123, c124, c134, c234, m12, m13, m14, m23, m24, m34⟩, T1, T2, T3, T4, ⟨e1, e2, e3, e4⟩, o1, o2, o3, o4⟩

/-- Witness for `l14_newton_gauss`: the three diagonal midpoints are pairwise distinct. -/
theorem l14w_newton_gauss_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    midpoint ℝ (0 : ℂ) (2 + I) = 1 + 1/2 * I ∧
    midpoint ℝ (1 : ℂ) (2 * I) = 1/2 + I ∧
    midpoint ℝ (4 : ℂ) (-I) = 2 - 1/2 * I ∧
    (1 + 1/2 * I : ℂ) ≠ 1/2 + I ∧
    (1 + 1/2 * I : ℂ) ≠ 2 - 1/2 * I ∧
    (1/2 + I : ℂ) ≠ 2 - 1/2 * I := by
  refine ⟨l14wbP_base, ?_⟩
  simp only [l14b_midpoint]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_diag_midpoints_ne` (same configuration; the conclusion is a pure distinctness statement). -/
theorem l14w_diag_midpoints_ne_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    midpoint ℝ (0 : ℂ) (2 + I) ≠ midpoint ℝ (1 : ℂ) (2 * I) ∧ midpoint ℝ (0 : ℂ) (2 + I) ≠ midpoint ℝ (4 : ℂ) (-I) ∧ midpoint ℝ (1 : ℂ) (2 * I) ≠ midpoint ℝ (4 : ℂ) (-I) := by
  refine ⟨l14wbP_base, ?_⟩
  simp only [l14b_midpoint]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_orthocentres_collinear`: the orthocentres are explicit and not all equal. -/
theorem l14w_orthocentres_collinear_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧
    T1.orthocenter = 1 + I ∧
    T2.orthocenter = 2 + 2 * I ∧
    T3.orthocenter = 0 ∧
    T4.orthocenter = 0 ∧
    T1.orthocenter ≠ T2.orthocenter ∧
    T1.orthocenter ≠ T3.orthocenter ∧
    T1.orthocenter ≠ T4.orthocenter ∧
    T2.orthocenter ≠ T3.orthocenter ∧
    T2.orthocenter ≠ T4.orthocenter ∧
    T3.orthocenter = T4.orthocenter := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbP_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  refine ⟨o1, o2, o3, o4, ?_⟩
  simp only [o1, o2, o3, o4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_orthocentres_not_all_eq`. -/
theorem l14w_orthocentres_not_all_eq_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧
    (T3.orthocenter ≠ T4.orthocenter ∨ T2.orthocenter ≠ T4.orthocenter) := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbP_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  right
  rw [o2, o4]
  norm_num [Complex.ext_iff]

/-- Witness for `l14_bodenmiller`: explicit common powers; the three circles have distinct centres and the orthocentres are distinct. -/
theorem l14w_bodenmiller_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -1 ∧
    (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -1 ∧
    (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T1.orthocenter = -1 ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 2 ∧
    (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 2 ∧
    (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T2.orthocenter = 2 ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 0 ∧
    (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 0 ∧
    (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T3.orthocenter = 0 ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = 0 ∧
    (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = 0 ∧
    (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).power T4.orthocenter = 0 ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    (⟨midpoint ℝ (0 : ℂ) (2 + I), dist (0 : ℂ) (2 + I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    (⟨midpoint ℝ (1 : ℂ) (2 * I), dist (1 : ℂ) (2 * I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ≠ (⟨midpoint ℝ (4 : ℂ) (-I), dist (4 : ℂ) (-I) / 2⟩ : EuclideanGeometry.Sphere ℂ).center ∧
    T1.orthocenter ≠ T2.orthocenter ∧
    T1.orthocenter ≠ T3.orthocenter ∧
    T1.orthocenter ≠ T4.orthocenter ∧
    T2.orthocenter ≠ T3.orthocenter ∧
    T2.orthocenter ≠ T4.orthocenter ∧
    T3.orthocenter = T4.orthocenter := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbP_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  simp only [o1, o2, o3, o4]
  simp only [EuclideanGeometry.Sphere.power, l14b_midpoint, Complex.dist_eq, div_pow, Complex.sq_norm]
  norm_num [Complex.ext_iff, Complex.normSq_apply]

/-- Witness for `l14_orthocentre_line_perp`: both directions are nonzero (genuine lines). -/
theorem l14w_orthocentre_line_perp_perp :
    ((0 : ℂ) ≠ 1 ∧
    (0 : ℂ) ≠ I ∧
    (-I : ℂ) ≠ -1 - 2 * I ∧
    (-2 + 3 * I : ℂ) ≠ 2 + I ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (0 : ℂ), I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), 1].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-I : ℂ), -1 - 2 * I] ∧
    ¬ line[ℝ, (0 : ℂ), I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    ¬ line[ℝ, (-I : ℂ), -1 - 2 * I].Parallel line[ℝ, (-2 + 3 * I : ℂ), 2 + I] ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), 1] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    (¬ ∃ z, z ∈ line[ℝ, (0 : ℂ), I] ∧ z ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ z ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((0 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (0 : ℂ) ∈ line[ℝ, (0 : ℂ), I]) ∧
    ((1 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (1 : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((4 : ℂ) ∈ line[ℝ, (0 : ℂ), 1] ∧ (4 : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((-I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (-I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I]) ∧
    ((2 * I : ℂ) ∈ line[ℝ, (0 : ℂ), I] ∧ (2 * I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I]) ∧
    ((2 + I : ℂ) ∈ line[ℝ, (-I : ℂ), -1 - 2 * I] ∧ (2 + I : ℂ) ∈ line[ℝ, (-2 + 3 * I : ℂ), 2 + I])) ∧
    ∃ T1 T2 T3 T4 : Affine.Triangle ℝ ℂ, (T1.points = ![(-I : ℂ), 2 * I, 2 + I] ∧ T2.points = ![(1 : ℂ), 4, 2 + I] ∧ T3.points = ![(0 : ℂ), 4, 2 * I] ∧ T4.points = ![(0 : ℂ), 1, -I]) ∧
    midpoint ℝ (1 : ℂ) (2 * I) - midpoint ℝ (0 : ℂ) (2 + I) ≠ 0 ∧ T2.orthocenter - T1.orthocenter ≠ 0 ∧
    inner ℝ (midpoint ℝ (1 : ℂ) (2 * I) - midpoint ℝ (0 : ℂ) (2 + I)) (T2.orthocenter - T1.orthocenter) = 0 := by
  obtain ⟨B, T1, T2, T3, T4, E, o1, o2, o3, o4⟩ := l14wbP_master
  refine ⟨B, T1, T2, T3, T4, E, ?_⟩
  rw [o1, o2]
  simp only [l14b_midpoint, Complex.inner, map_sub, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]
  norm_num [Complex.ext_iff]

end QuadNewton
