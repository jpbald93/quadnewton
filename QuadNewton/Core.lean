import QuadNewton.Lines

/-!
# Core identities in normal coordinates

With `A₁₂ = 0`, `A₁₃ = u`, `A₂₃ = w`, `A₁₄ = s u`, `A₂₄ = t w`, `A₃₄ = nX u w s t`, the four
orthocentres are `h4 + r • dv` for explicit real `r`, the midpoints of the diagonals are
`X/2`, `(u + t w)/2`, `(s u + w)/2`, and the polynomial identities behind the Newton–Gauss line,
the orthocentre line, Bodenmiller's theorem and the perpendicularity are checked here.
-/

open Complex ComplexConjugate

namespace QuadNewton

lemma normSq_cast (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = z * conj z := (Complex.mul_conj z).symm

lemma circ_add (a b c o : ℂ) : circ (o + a) (o + b) (o + c) = o + circ a b c := by
  unfold circ; simp only [add_sub_add_left_eq_sub]; ring

lemma ortho_add (a b c o : ℂ) : ortho (o + a) (o + b) (o + c) = o + ortho a b c := by
  unfold ortho; rw [circ_add]; ring

lemma ortho_add0 (b c o : ℂ) : ortho o (o + b) (o + c) = o + ortho 0 b c := by
  simpa using ortho_add 0 b c o

/-- Certificate form of the orthocentre formula. -/
lemma ortho_eq_of (a b c H : ℂ)
    (hD : conj (b - a) * (c - a) - (b - a) * conj (c - a) ≠ 0)
    (hH : (b + c - a - H) * (conj (b - a) * (c - a) - (b - a) * conj (c - a)) =
      2 * ((b - a) * conj (b - a) * (c - a) - (c - a) * conj (c - a) * (b - a))) :
    ortho a b c = H := by
  unfold ortho circ
  rw [normSq_cast, normSq_cast]
  field_simp
  linear_combination hH

lemma D_eq (u w : ℂ) : conj w * u - conj u * w = -2 * I * (cr u w : ℂ) := by
  apply Complex.ext <;> simp [cr, Complex.mul_re, Complex.mul_im] <;> ring

lemma D_ne {u w : ℂ} (h : cr u w ≠ 0) : conj w * u - conj u * w ≠ 0 := by
  rw [D_eq]; simp [h, Complex.I_ne_zero]

lemma conj_D (u w : ℂ) : conj (conj w * u - conj u * w) = -(conj w * u - conj u * w) := by
  simp only [map_sub, map_mul, Complex.conj_conj]; ring

lemma conj_nX (u w : ℂ) (s t : ℝ) :
    conj (nX u w s t) = ((s : ℂ) * (1 - t) * conj u + (t : ℂ) * (s - 1) * conj w) / ((s : ℂ) - t) := by
  unfold nX; simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_ofReal, map_one]

/-- `Re (conj u * w)`. -/
noncomputable def pr (u w : ℂ) : ℝ := (conj u * w).re

lemma pr_cast (u w : ℂ) : ((pr u w : ℝ) : ℂ) = (conj u * w + conj w * u) / 2 := by
  unfold pr; rw [Complex.re_eq_add_conj]; simp only [map_mul, Complex.conj_conj]; ring

/-- The orthocentre of `T₄` in normal coordinates. -/
noncomputable def h4 (u w : ℂ) : ℂ := (u - w) * (conj u * w + conj w * u) / (conj w * u - conj u * w)

/-- A direction vector of the line of orthocentres. -/
noncomputable def dv (u w : ℂ) (s t : ℝ) : ℂ :=
  (((s : ℂ) - 1) * u - ((t : ℂ) - 1) * w) / (conj w * u - conj u * w)

lemma conj_dv (u w : ℂ) (s t : ℝ) : conj (dv u w s t) =
    -((((s : ℂ) - 1) * conj u - ((t : ℂ) - 1) * conj w) / (conj w * u - conj u * w)) := by
  unfold dv; rw [map_div₀, conj_D, div_neg]; congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, map_one]

lemma conj_h4 (u w : ℂ) : conj (h4 u w) =
    -((conj u - conj w) * (conj u * w + conj w * u) / (conj w * u - conj u * w)) := by
  unfold h4; rw [map_div₀, conj_D, div_neg]; congr 1
  simp only [map_sub, map_mul, map_add, Complex.conj_conj]; ring

lemma re_mul_conj (A B : ℂ) : (((A * conj B).re : ℝ) : ℂ) = (A * conj B + conj A * B) / 2 := by
  rw [Complex.re_eq_add_conj]; simp only [map_mul, Complex.conj_conj]

noncomputable def r3 (u w : ℂ) : ℝ := 2 * pr u w
noncomputable def r2 (u w : ℂ) (s t : ℝ) : ℝ := -2 * s * (Complex.normSq u - pr u w) / (s - t)
noncomputable def r1 (u w : ℂ) (s t : ℝ) : ℝ := 2 * t * (Complex.normSq w - pr u w) / (s - t)

section
variable {u w : ℂ} {s t : ℝ}

lemma cne {x : ℝ} (h : x ≠ 0) : (x : ℂ) ≠ 0 := by exact_mod_cast h
lemma cne1 {x y : ℝ} (h : x ≠ y) : (x : ℂ) - y ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast h

theorem ortho_T4 (huw : cr u w ≠ 0) : ortho 0 u w = h4 u w := by
  have hD := D_ne huw
  apply ortho_eq_of
  · simp only [sub_zero]; intro e; apply hD; linear_combination -e
  · simp only [sub_zero]; unfold h4
    generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
    have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
    have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
    field_simp; ring

theorem ortho_T3 (huw : cr u w ≠ 0) (s0 : s ≠ 0) (t0 : t ≠ 0) :
    ortho 0 ((s : ℂ) * u) ((t : ℂ) * w) = h4 u w + (r3 u w : ℂ) * dv u w s t := by
  have hD := D_ne huw
  have hs := cne s0; have ht := cne t0
  have e : conj ((s : ℂ) * u - 0) * ((t : ℂ) * w - 0) - ((s : ℂ) * u - 0) * conj ((t : ℂ) * w - 0)
      = -(s : ℂ) * t * (conj w * u - conj u * w) := by
    simp only [sub_zero, map_mul, Complex.conj_ofReal]; ring
  apply ortho_eq_of
  · rw [e]; simp [hs, ht, hD]
  · rw [e]; unfold h4 dv r3; push_cast; rw [pr_cast]
    simp only [sub_zero, map_mul, Complex.conj_ofReal]
    generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
    have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
    have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
    field_simp; ring

theorem ortho_T2 (huw : cr u w ≠ 0) (s0 : s ≠ 0) (s1 : s ≠ 1) (t0 : t ≠ 0) (st : s ≠ t) :
    ortho u ((s : ℂ) * u) (nX u w s t) = h4 u w + (r2 u w s t : ℂ) * dv u w s t := by
  have hD := D_ne huw
  have hs := cne s0; have ht := cne t0; have hst := cne1 st
  have hs1 : (s : ℂ) - 1 ≠ 0 := by simpa using cne1 s1
  have e : conj ((s : ℂ) * u - u) * (nX u w s t - u) - ((s : ℂ) * u - u) * conj (nX u w s t - u)
      = -(t : ℂ) * (s - 1) ^ 2 / (s - t) * (conj w * u - conj u * w) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
    field_simp; ring
  apply ortho_eq_of
  · rw [e]; simp [ht, hD, hs1, hst]
  · rw [e]; unfold h4 dv r2; push_cast; rw [pr_cast, normSq_cast]
    simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
    generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
    have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
    have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
    have hst2 : -(t : ℂ) + s ≠ 0 := by intro h; apply hst; linear_combination h
    field_simp; ring

theorem ortho_T1 (huw : cr u w ≠ 0) (s0 : s ≠ 0) (t1 : t ≠ 1) (st : s ≠ t) :
    ortho w ((t : ℂ) * w) (nX u w s t) = h4 u w + (r1 u w s t : ℂ) * dv u w s t := by
  have hD := D_ne huw
  have hs := cne s0; have hst := cne1 st
  have ht1 : (t : ℂ) - 1 ≠ 0 := by simpa using cne1 t1
  have e : conj ((t : ℂ) * w - w) * (nX u w s t - w) - ((t : ℂ) * w - w) * conj (nX u w s t - w)
      = -(s : ℂ) * (t - 1) ^ 2 / (s - t) * (conj w * u - conj u * w) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
    field_simp; ring
  apply ortho_eq_of
  · rw [e]; simp [hs, hD, ht1, hst]
  · rw [e]; unfold h4 dv r1; push_cast; rw [pr_cast, normSq_cast]
    simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
    generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
    have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
    have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
    have hst2 : -(t : ℂ) + s ≠ 0 := by intro h; apply hst; linear_combination h
    field_simp; ring

/-- The cross product vanishes iff `conj a * b` is real. -/
lemma cr_eq_zero_iff (a b : ℂ) : cr a b = 0 ↔ conj a * b = a * conj b := by
  unfold cr
  rw [← Complex.conj_eq_iff_im]
  simp only [map_mul, Complex.conj_conj]
  constructor <;> intro h <;> exact h.symm

/-- Newton–Gauss identity in normal coordinates. -/
theorem newton_core (st : s ≠ t) :
    cr (u + (t : ℂ) * w - nX u w s t) ((s : ℂ) * u + w - nX u w s t) = 0 := by
  have hst := cne1 st
  rw [cr_eq_zero_iff]
  simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
  generalize conj u = U; generalize conj w = W
  field_simp; ring

/-- The direction of the orthocentre line is perpendicular to the Newton–Gauss line. -/
theorem perp_core (huw : cr u w ≠ 0) (st : s ≠ t) :
    ((u + (t : ℂ) * w - nX u w s t) * conj (dv u w s t)).re = 0 := by
  have hD := D_ne huw; have hst := cne1 st
  apply Complex.ofReal_injective
  rw [re_mul_conj, Complex.ofReal_zero]
  simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, conj_nX, conj_dv]
  simp only [dv, nX]
  generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
  have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
  have hD'' : U * w - W * u ≠ 0 := by intro h; apply hD; linear_combination -h
  have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
  field_simp; ring

/-- Power of a point with respect to the circle on diameter `P Q`. -/
noncomputable def pw (z P Q : ℂ) : ℝ := ‖z - (P + Q) / 2‖ ^ 2 - ‖P - Q‖ ^ 2 / 4

lemma pw_eq (z P Q : ℂ) : pw z P Q = ((z - P) * conj (z - Q)).re := by
  simp only [pw, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.div_re, Complex.div_im]
  norm_num; ring

lemma pw_add (z P Q o : ℂ) : pw (o + z) (o + P) (o + Q) = pw z P Q := by
  rw [pw_eq, pw_eq]; congr 2 <;> ring_nf

lemma pw_add0 (z Q o : ℂ) : pw (o + z) o (o + Q) = pw z 0 Q := by
  simpa using pw_add z 0 Q o

/-- Every point of the orthocentre line has equal power w.r.t. the circles on the diagonals. -/
theorem pw_core (huw : cr u w ≠ 0) (st : s ≠ t) (r : ℝ) :
    pw (h4 u w + (r : ℂ) * dv u w s t) 0 (nX u w s t) =
      pw (h4 u w + (r : ℂ) * dv u w s t) u ((t : ℂ) * w) ∧
    pw (h4 u w + (r : ℂ) * dv u w s t) 0 (nX u w s t) =
      pw (h4 u w + (r : ℂ) * dv u w s t) ((s : ℂ) * u) w := by
  have hD := D_ne huw; have hst := cne1 st
  constructor <;>
  · rw [pw_eq, pw_eq]
    apply Complex.ofReal_injective
    rw [re_mul_conj, re_mul_conj]
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, conj_nX, conj_dv, conj_h4, map_zero]
    simp only [h4, dv, nX]
    generalize conj u = U at hD ⊢; generalize conj w = W at hD ⊢
    have hD' : u * W - w * U ≠ 0 := by intro h; apply hD; linear_combination h
    have hD'' : U * w - W * u ≠ 0 := by intro h; apply hD; linear_combination -h
    have hD3 : -(u * W) + w * U ≠ 0 := by intro h; apply hD; linear_combination -h
    field_simp; ring

theorem dv_ne (huw : cr u w ≠ 0) (s1 : s ≠ 1) : dv u w s t ≠ 0 := by
  have hD := D_ne huw
  unfold dv
  refine div_ne_zero ?_ hD
  intro h
  have := (indep huw (x := s - 1) (y := -(t - 1)) (by push_cast; linear_combination h)).1
  exact s1 (by linarith)

theorem mid_ne (huw : cr u w ≠ 0) (s1 : s ≠ 1) (t0 : t ≠ 0) (st : s ≠ t) :
    u + (t : ℂ) * w - nX u w s t ≠ 0 := by
  have hst := cne1 st
  intro h
  unfold nX at h
  rw [sub_eq_zero, eq_div_iff hst] at h
  have := (indep huw (x := t * (s - 1)) (y := t * (1 - t))
    (by push_cast; linear_combination h)).1
  rcases mul_eq_zero.mp this with h1 | h1
  · exact t0 h1
  · exact s1 (by linarith)

/-- Not all four orthocentres coincide: `r3 ≠ 0` or `r2 ≠ 0`. -/
theorem r_ne (huw : cr u w ≠ 0) (s0 : s ≠ 0) (st : s ≠ t) : r3 u w ≠ 0 ∨ r2 u w s t ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h3, h2⟩ := hc
  have hu : u ≠ 0 := by rintro rfl; apply huw; simp [cr]
  have p0 : pr u w = 0 := by unfold r3 at h3; linarith
  have hst : s - t ≠ 0 := sub_ne_zero.mpr st
  unfold r2 at h2
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · rw [p0, sub_zero] at h2
    have : Complex.normSq u = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exfalso; apply s0; linarith
      · exact h
    exact hu (Complex.normSq_eq_zero.mp this)
  · exact hst h2

end

end QuadNewton
