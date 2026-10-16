import QuadNewton.Core

/-!
# The diagonal / orthocentre side of the complete quadrilateral

For lines `L₁ L₂ L₃ L₄` in general position, write `Aᵢⱼ = meet Lᵢ Lⱼ`. The diagonals are
`(A₁₂, A₃₄)`, `(A₁₃, A₂₄)`, `(A₁₄, A₂₃)`, the triangles are
`T₄ = (A₁₂, A₁₃, A₂₃)`, `T₃ = (A₁₂, A₁₄, A₂₄)`, `T₂ = (A₁₃, A₁₄, A₃₄)`, `T₁ = (A₂₃, A₂₄, A₃₄)`.

* `newton_gauss`: the midpoints of the three diagonals are collinear.
* `orthocentres_collinear`: the orthocentres of `T₁ … T₄` are collinear.
* `bodenmiller`: every orthocentre has equal power w.r.t. the three circles on the diagonals.
* `orthocentre_line_perp`: the orthocentre line is perpendicular to the Newton–Gauss line.
* `diag_midpoints_ne`, `orthocentres_not_all_eq`: the two lines are determined.
-/

open Complex ComplexConjugate

namespace QuadNewton

/-- Points of the form `p₀ + r v` are collinear. -/
lemma collinear_of_param {s : Set ℂ} (p₀ v : ℂ) (h : ∀ p ∈ s, ∃ r : ℝ, p = p₀ + (r : ℂ) * v) :
    Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨p₀, v, fun p hp => ?_⟩
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r, by rw [hr, vadd_eq_add, Complex.real_smul]; ring⟩

section
variable {L₁ L₂ L₃ L₄ : Line}

/-- The orthocentres in normal coordinates. -/
lemma orthos_nc (h : GenPos L₁ L₂ L₃ L₄) :
    ∃ (O u w : ℂ) (s t : ℝ),
      meet L₁ L₂ = O ∧ meet L₁ L₃ = O + u ∧ meet L₂ L₃ = O + w ∧
      meet L₁ L₄ = O + (s : ℂ) * u ∧ meet L₂ L₄ = O + (t : ℂ) * w ∧
      meet L₃ L₄ = O + nX u w s t ∧
      cr u w ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 ∧ t ≠ 0 ∧ t ≠ 1 ∧ s ≠ t ∧
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) = O + h4 u w ∧
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) = O + h4 u w + (r3 u w : ℂ) * dv u w s t ∧
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) = O + h4 u w + (r2 u w s t : ℂ) * dv u w s t ∧
      ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄) = O + h4 u w + (r1 u w s t : ℂ) * dv u w s t := by
  obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
    normal_coords h
  refine ⟨O, u, w, s, t, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, ?_, ?_, ?_, ?_⟩
  · rw [h12, h13, h23, ortho_add0, ortho_T4 huw]
  · rw [h12, h14, h24, ortho_add0, ortho_T3 huw s0 t0, add_assoc]
  · rw [h13, h14, h34, ortho_add, ortho_T2 huw s0 s1 t0 st, add_assoc]
  · rw [h23, h24, h34, ortho_add, ortho_T1 huw s0 t1 st, add_assoc]

/-- **Newton–Gauss line**: the midpoints of the three diagonals of a complete quadrilateral
are collinear. -/
theorem newton_gauss (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ {(meet L₁ L₂ + meet L₃ L₄) / 2, (meet L₁ L₃ + meet L₂ L₄) / 2,
      (meet L₁ L₄ + meet L₂ L₃) / 2} := by
  obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
    normal_coords h
  rw [h12, h13, h23, h14, h24, h34]
  have hv := mid_ne huw s1 t0 st
  obtain ⟨r, hr⟩ := par_of_cr hv (newton_core st)
  refine collinear_of_param (O + nX u w s t / 2) ((u + (t : ℂ) * w - nX u w s t) / 2) ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by push_cast; ring⟩
  · exact ⟨1, by push_cast; ring⟩
  · exact ⟨r, by linear_combination hr / 2⟩

/-- The Newton–Gauss line is well defined: the midpoints of the first two diagonals differ. -/
theorem diag_midpoints_ne (h : GenPos L₁ L₂ L₃ L₄) :
    (meet L₁ L₂ + meet L₃ L₄) / 2 ≠ (meet L₁ L₃ + meet L₂ L₄) / 2 := by
  obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
    normal_coords h
  rw [h12, h13, h24, h34]
  intro e; apply mid_ne huw s1 t0 st; linear_combination -2 * e

/-- **Orthocentre line** (Steiner): the orthocentres of the four triangles of a complete
quadrilateral are collinear. -/
theorem orthocentres_collinear (h : GenPos L₁ L₂ L₃ L₄) :
    Collinear ℝ {ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} := by
  obtain ⟨O, u, w, s, t, -, -, -, -, -, -, -, -, -, -, -, -, H4, H3, H2, H1⟩ := orthos_nc h
  rw [H1, H2, H3, H4]
  refine collinear_of_param (O + h4 u w) (dv u w s t) ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

/-- The orthocentre line is well defined: the four orthocentres are not all equal
(although two of them may coincide, see `README.md`). -/
theorem orthocentres_not_all_eq (h : GenPos L₁ L₂ L₃ L₄) :
    ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄) ≠ ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) ∨
    ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄) ≠ ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃) := by
  obtain ⟨O, u, w, s, t, -, -, -, -, -, -, huw, s0, s1, -, -, st, H4, H3, H2, -⟩ := orthos_nc h
  rw [H4, H3, H2]
  have hd := dv_ne huw s1 (t := t)
  rcases r_ne huw s0 st with hr | hr
  · left; intro e; apply hr
    have : (r3 u w : ℂ) * dv u w s t = 0 := by linear_combination e
    exact_mod_cast (mul_eq_zero.mp this).resolve_right hd
  · right; intro e; apply hr
    have : (r2 u w s t : ℂ) * dv u w s t = 0 := by linear_combination e
    exact_mod_cast (mul_eq_zero.mp this).resolve_right hd

/-- Every orthocentre lies on the line `O + h4 + ℝ • dv`, in normal coordinates. -/
lemma orthos_on_line (h : GenPos L₁ L₂ L₃ L₄) :
    ∃ (O u w : ℂ) (s t : ℝ), cr u w ≠ 0 ∧ s ≠ t ∧
      meet L₁ L₂ = O ∧ meet L₁ L₃ = O + u ∧ meet L₂ L₃ = O + w ∧
      meet L₁ L₄ = O + (s : ℂ) * u ∧ meet L₂ L₄ = O + (t : ℂ) * w ∧
      meet L₃ L₄ = O + nX u w s t ∧
      ∀ H ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
        ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
        ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
        ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
        ∃ r : ℝ, H = O + h4 u w + (r : ℂ) * dv u w s t := by
  obtain ⟨O, u, w, s, t, h12, h13, h23, h14, h24, h34, huw, -, -, -, -, st, H4, H3, H2, H1⟩ :=
    orthos_nc h
  refine ⟨O, u, w, s, t, huw, st, h12, h13, h23, h14, h24, h34, fun H hH => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
  rcases hH with rfl | rfl | rfl | rfl
  · exact ⟨_, H1⟩
  · exact ⟨_, H2⟩
  · exact ⟨_, H3⟩
  · exact ⟨0, by rw [H4]; simp⟩

/-- **Bodenmiller's theorem** (coaxality of the diagonal circles, via the orthocentres): each of
the four orthocentres has the same power with respect to the three circles having the diagonals
as diameters. Here `pw z P Q = ‖z - (P + Q)/2‖² - ‖P - Q‖²/4`. -/
theorem bodenmiller (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      pw H (meet L₁ L₂) (meet L₃ L₄) = pw H (meet L₁ L₃) (meet L₂ L₄) ∧
      pw H (meet L₁ L₂) (meet L₃ L₄) = pw H (meet L₁ L₄) (meet L₂ L₃) := by
  obtain ⟨O, u, w, s, t, huw, st, h12, h13, h23, h14, h24, h34, hl⟩ := orthos_on_line h
  intro H hH
  obtain ⟨r, rfl⟩ := hl H hH
  rw [h12, h13, h23, h14, h24, h34, add_assoc O]
  constructor
  · rw [pw_add0, ← add_zero u, pw_add, add_zero]
    exact (pw_core huw st r).1
  · rw [pw_add0, ← add_zero w, pw_add, add_zero]
    exact (pw_core huw st r).2

/-- **Perpendicularity**: the line of the orthocentres is perpendicular to the Newton–Gauss line.
For the midpoints `m₁` of `(A₁₂, A₃₄)` and `m₂` of `(A₁₃, A₂₄)` and any two orthocentres
`H₁ H₂`, `Re ((m₂ - m₁) * conj (H₂ - H₁)) = 0`. -/
theorem orthocentre_line_perp (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H₁ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
    ∀ H₂ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      (((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) * conj (H₂ - H₁)).re = 0 := by
  obtain ⟨O, u, w, s, t, huw, st, h12, h13, h23, h14, h24, h34, hl⟩ := orthos_on_line h
  intro H₁ hH₁ H₂ hH₂
  obtain ⟨r₁, rfl⟩ := hl H₁ hH₁
  obtain ⟨r₂, rfl⟩ := hl H₂ hH₂
  rw [h12, h13, h24, h34]
  have e : (O + u + (O + (t : ℂ) * w)) / 2 - (O + (O + nX u w s t)) / 2 =
      ((1 / 2 : ℝ) : ℂ) * (u + (t : ℂ) * w - nX u w s t) := by push_cast; ring
  have e2 : O + h4 u w + (r₂ : ℂ) * dv u w s t - (O + h4 u w + (r₁ : ℂ) * dv u w s t) =
      ((r₂ - r₁ : ℝ) : ℂ) * dv u w s t := by push_cast; ring
  rw [e, e2, map_mul, Complex.conj_ofReal, mul_mul_mul_comm, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, perp_core huw st, mul_zero]

end

end QuadNewton
