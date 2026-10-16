import QuadNewton.Basic

/-!
# Incidence lemmas and normal coordinates for the complete quadrilateral

`meet_mem_left`, `meet_mem_right`: the intersection point lies on both lines.
`normal_coords`: under `GenPos`, with `O = A₁₂`, `u = A₁₃ - O`, `w = A₂₃ - O`, there are reals
`s t` with `A₁₄ = O + s u`, `A₂₄ = O + t w` and `A₃₄ = O + nX u w s t`, together with the
nondegeneracies `cr u w ≠ 0`, `s ≠ 0, 1`, `t ≠ 0, 1`, `s ≠ t`.
-/

open Complex ComplexConjugate

namespace QuadNewton

lemma cr_def (a b : ℂ) : cr a b = a.re * b.im - a.im * b.re := by
  simp [cr, Complex.mul_im]; ring

lemma mem_carrier {L : Line} {z : ℂ} : z ∈ L.carrier ↔ cr L.d (z - L.p) = 0 := Iff.rfl

lemma cr_comm (a b : ℂ) : cr b a = - cr a b := by rw [cr_def, cr_def]; ring

lemma cr_self (a : ℂ) : cr a a = 0 := by rw [cr_def]; ring

lemma cr_lin (a b c : ℂ) (x y : ℝ) : cr a ((x : ℂ) * b + (y : ℂ) * c) = x * cr a b + y * cr a c := by
  simp only [cr_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]; ring

lemma cr_smul (a b : ℂ) (x y : ℝ) : cr ((x : ℂ) * a) ((y : ℂ) * b) = x * y * cr a b := by
  simp only [cr_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma cr_sub (a b c : ℂ) : cr a (b - c) = cr a b - cr a c := by
  simp only [cr_def, Complex.sub_re, Complex.sub_im]; ring

/-- The intersection point lies on the first line. -/
theorem meet_mem_left (L M : Line) : meet L M ∈ L.carrier := by
  rw [mem_carrier]; unfold meet
  rw [add_sub_cancel_left]
  simp only [cr_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- The intersection point lies on the second line (when the lines are not parallel). -/
theorem meet_mem_right (L M : Line) (h : cr M.d L.d ≠ 0) : meet L M ∈ M.carrier := by
  rw [mem_carrier]; unfold meet
  have e : L.p + ((cr M.d (M.p - L.p) / cr M.d L.d : ℝ) : ℂ) * L.d - M.p =
      ((-1 : ℝ) : ℂ) * (M.p - L.p) + ((cr M.d (M.p - L.p) / cr M.d L.d : ℝ) : ℂ) * L.d := by
    push_cast; ring
  rw [e, cr_lin]; field_simp; ring

/-- A vector with zero cross product against a nonzero direction is a real multiple of it. -/
lemma par_of_cr {d v : ℂ} (hd : d ≠ 0) (h : cr d v = 0) : ∃ r : ℝ, v = r * d := by
  have hN : d.re ^ 2 + d.im ^ 2 ≠ 0 := by
    intro h0; apply hd; apply Complex.ext <;> simp <;> nlinarith [sq_nonneg d.re, sq_nonneg d.im]
  rw [cr_def] at h
  refine ⟨(d.re * v.re + d.im * v.im) / (d.re ^ 2 + d.im ^ 2), ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; field_simp
    linear_combination (-d.im) * h
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; field_simp
    linear_combination (d.re) * h

lemma diff_of_mem {L : Line} {z y : ℂ} (hd : L.d ≠ 0) (hz : z ∈ L.carrier) (hy : y ∈ L.carrier) :
    ∃ r : ℝ, z - y = r * L.d := by
  apply par_of_cr hd
  rw [mem_carrier] at hz hy
  have : z - y = (z - L.p) - (y - L.p) := by ring
  rw [this, cr_sub, hz, hy, sub_zero]

/-- Real linear independence of two vectors with nonzero cross product. -/
lemma indep {u w : ℂ} (h : cr u w ≠ 0) {x y : ℝ} (e : (x : ℂ) * u + (y : ℂ) * w = 0) :
    x = 0 ∧ y = 0 := by
  rw [cr_def] at h
  have e1 := congrArg Complex.re e
  have e2 := congrArg Complex.im e
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at e1 e2
  constructor
  · have : x * (u.re * w.im - u.im * w.re) = 0 := by linear_combination w.im * e1 - w.re * e2
    exact (mul_eq_zero.mp this).resolve_right h
  · have : y * (u.re * w.im - u.im * w.re) = 0 := by linear_combination u.re * e2 - u.im * e1
    exact (mul_eq_zero.mp this).resolve_right h

/-- The normal-coordinate expression of the vertex `A₃₄ - A₁₂`. -/
noncomputable def nX (u w : ℂ) (s t : ℝ) : ℂ :=
  ((s : ℂ) * (1 - t) * u + (t : ℂ) * (s - 1) * w) / ((s : ℂ) - t)

section
variable {L₁ L₂ L₃ L₄ : Line}

lemma GenPos.mem (h : GenPos L₁ L₂ L₃ L₄) :
    meet L₁ L₂ ∈ L₁.carrier ∧ meet L₁ L₂ ∈ L₂.carrier ∧ meet L₁ L₃ ∈ L₁.carrier ∧
    meet L₁ L₃ ∈ L₃.carrier ∧ meet L₁ L₄ ∈ L₁.carrier ∧ meet L₁ L₄ ∈ L₄.carrier ∧
    meet L₂ L₃ ∈ L₂.carrier ∧ meet L₂ L₃ ∈ L₃.carrier ∧ meet L₂ L₄ ∈ L₂.carrier ∧
    meet L₂ L₄ ∈ L₄.carrier ∧ meet L₃ L₄ ∈ L₃.carrier ∧ meet L₃ L₄ ∈ L₄.carrier := by
  have r : ∀ {a b : ℂ}, cr a b ≠ 0 → cr b a ≠ 0 := fun hh => by rw [cr_comm]; exact neg_ne_zero.mpr hh
  exact ⟨meet_mem_left _ _, meet_mem_right _ _ (r h.p12), meet_mem_left _ _,
    meet_mem_right _ _ (r h.p13), meet_mem_left _ _, meet_mem_right _ _ (r h.p14),
    meet_mem_left _ _, meet_mem_right _ _ (r h.p23), meet_mem_left _ _,
    meet_mem_right _ _ (r h.p24), meet_mem_left _ _, meet_mem_right _ _ (r h.p34)⟩

/-- Normal coordinates of a complete quadrilateral in general position. -/
theorem normal_coords (h : GenPos L₁ L₂ L₃ L₄) :
    ∃ (O u w : ℂ) (s t α β : ℝ),
      meet L₁ L₂ = O ∧ meet L₁ L₃ = O + u ∧ meet L₂ L₃ = O + w ∧
      meet L₁ L₄ = O + (s : ℂ) * u ∧ meet L₂ L₄ = O + (t : ℂ) * w ∧
      meet L₃ L₄ = O + nX u w s t ∧
      cr u w ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 ∧ t ≠ 0 ∧ t ≠ 1 ∧ s ≠ t ∧
      w - u = (α : ℂ) * L₃.d ∧ (t : ℂ) * w - (s : ℂ) * u = (β : ℂ) * L₄.d ∧ α ≠ 0 ∧ β ≠ 0 := by
  obtain ⟨m12a, m12b, m13a, m13b, m14a, m14b, m23a, m23b, m24a, m24b, m34a, m34b⟩ := h.mem
  set O := meet L₁ L₂
  obtain ⟨a, ha⟩ := diff_of_mem h.d₁ m13a m12a
  obtain ⟨b, hb⟩ := diff_of_mem h.d₁ m14a m12a
  obtain ⟨c, hc⟩ := diff_of_mem h.d₂ m23a m12b
  obtain ⟨e, he⟩ := diff_of_mem h.d₂ m24a m12b
  have ne : ∀ {L : Line} {x y : ℂ}, x ∈ L.carrier → y ∉ L.carrier → x ≠ y :=
    fun hx hy hxy => hy (hxy ▸ hx)
  have a0 : a ≠ 0 := by
    rintro rfl; apply ne m13b h.c123; simpa [sub_eq_zero] using ha
  have c0 : c ≠ 0 := by
    rintro rfl; apply ne m23b h.c123; simpa [sub_eq_zero] using hc
  set u := meet L₁ L₃ - O with hu
  set w := meet L₂ L₃ - O with hw
  have huw : cr u w ≠ 0 := by
    rw [ha, hc, cr_smul]; exact mul_ne_zero (mul_ne_zero a0 c0) h.p12
  set s := b / a
  set t := e / c
  have hsu : meet L₁ L₄ = O + (s : ℂ) * u := by
    rw [ha]; have : meet L₁ L₄ = O + b * L₁.d := by rw [← hb]; ring
    rw [this]; simp only [s]; push_cast
    have : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast a0
    field_simp
  have htw : meet L₂ L₄ = O + (t : ℂ) * w := by
    rw [hc]; have : meet L₂ L₄ = O + e * L₂.d := by rw [← he]; ring
    rw [this]; simp only [t]; push_cast
    have : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast c0
    field_simp
  have s0 : s ≠ 0 := by
    intro hs; apply ne m14b h.c124; rw [hsu, hs]; simp; rfl
  have t0 : t ≠ 0 := by
    intro ht; apply ne m24b h.c124; rw [htw, ht]; simp; rfl
  have s1 : s ≠ 1 := by
    intro hs; apply ne m14b h.c134; rw [hsu, hs, hu]; simp
  have t1 : t ≠ 1 := by
    intro ht; apply ne m24b h.c234; rw [htw, ht, hw]; simp
  obtain ⟨α, hα⟩ := diff_of_mem h.d₃ m23b m13b
  obtain ⟨β, hβ⟩ := diff_of_mem h.d₄ m24b m14b
  have hα' : w - u = α * L₃.d := by rw [← hα, hu, hw]; ring
  have hβ' : (t : ℂ) * w - (s : ℂ) * u = β * L₄.d := by rw [← hβ, hsu, htw]; ring
  have α0 : α ≠ 0 := by
    rintro rfl
    have := (indep huw (x := -1) (y := 1) (by push_cast at hα' ⊢; linear_combination hα')).2
    norm_num at this
  have β0 : β ≠ 0 := by
    rintro rfl
    have := (indep huw (x := -s) (y := t) (by push_cast at hβ' ⊢; linear_combination hβ')).2
    exact t0 this
  have st : s ≠ t := by
    intro hst
    have e1 : (β : ℂ) * L₄.d = ((s * α : ℝ) : ℂ) * L₃.d := by
      rw [← hβ', hst]; push_cast; linear_combination (t : ℂ) * hα'
    have := congrArg (cr L₃.d) e1
    rw [show cr L₃.d (β * L₄.d) = cr ((1:ℝ) * L₃.d) (β * L₄.d) by simp,
      show cr L₃.d (((s * α : ℝ) : ℂ) * L₃.d) = cr ((1:ℝ) * L₃.d) (((s * α : ℝ) : ℂ) * L₃.d) by simp,
      cr_smul, cr_smul, cr_self] at this
    simp at this
    rcases this with h1 | h1
    · exact β0 h1
    · exact h.p34 h1
  obtain ⟨γ, hγ⟩ := diff_of_mem h.d₃ m34a m13b
  obtain ⟨δ, hδ⟩ := diff_of_mem h.d₄ m34b m14b
  set g := γ / α
  set k := δ / β
  have hg : meet L₃ L₄ - O = u + (g : ℂ) * (w - u) := by
    rw [hα']; have : meet L₃ L₄ - O = u + γ * L₃.d := by rw [← hγ, hu]; ring
    rw [this]; simp only [g]; push_cast
    have : ((α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast α0
    field_simp
  have hk : meet L₃ L₄ - O = (s : ℂ) * u + (k : ℂ) * ((t : ℂ) * w - (s : ℂ) * u) := by
    rw [hβ']; have : meet L₃ L₄ - O = s * u + δ * L₄.d := by rw [← hδ, hsu]; ring
    rw [this]; simp only [k]; push_cast
    have : ((β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast β0
    field_simp
  obtain ⟨i1, i2⟩ := indep huw (x := 1 - g - s + k * s) (y := g - k * t)
    (by push_cast; linear_combination hk - hg)
  have hrel : (k : ℂ) * ((s : ℂ) - t) = s - 1 := by
    have : k * (s - t) = s - 1 := by linear_combination i1 + i2
    exact_mod_cast this
  have st' : (s : ℂ) - t ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast st
  refine ⟨O, u, w, s, t, α, β, rfl, by rw [hu]; ring, by rw [hw]; ring, hsu, htw, ?_, huw, s0, s1,
    t0, t1, st, hα', hβ', α0, β0⟩
  have : meet L₃ L₄ = O + (meet L₃ L₄ - O) := by ring
  rw [this, hk]; unfold nX; congr 1
  rw [eq_div_iff st']
  linear_combination ((t : ℂ) * w - (s : ℂ) * u) * hrel

end

end QuadNewton
