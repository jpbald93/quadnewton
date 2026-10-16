import QuadNewton.Quad

/-!
# Definition bridges to Mathlib

The local notions of `QuadNewton.Basic` and `QuadNewton.Core` agree with Mathlib's:

* `carrier_eq_line`: `Line.carrier` is the affine span `line[ℝ, p, p + d]`.
* `meet_eq_iff`: `meet L M` is the unique common point of two non-parallel lines.
* `circ_eq_circumcenter`, `ortho_eq_orthocenter`: `circ`, `ortho` are Mathlib's circumcentre
  and orthocentre of a non-collinear triangle.
* `foot_eq_orthogonalProjection`: `foot` is Mathlib's orthogonal projection onto the line.
* `genPos_triangles`: under `GenPos` the four triangles are non-collinear and the six vertices
  are pairwise distinct.
* `genPos_iff`: `GenPos` restated with `AffineSubspace.Parallel` and common points.
* `pw_eq_power`, `bodenmiller_coaxal`: `pw` is Mathlib's power of a point; Bodenmiller restated.
* `perp_iff_inner`: the perpendicularity condition is Mathlib's real inner product on `ℂ`.
-/

open Complex ComplexConjugate

namespace QuadNewton

/-- **B1.** The carrier of a line is Mathlib's affine line through `p` and `p + d`. -/
theorem carrier_eq_line (L : Line) (hd : L.d ≠ 0) :
    L.carrier = (line[ℝ, L.p, L.p + L.d] : Set ℂ) := by
  ext z
  rw [SetLike.mem_coe, ← vsub_vadd z L.p, vadd_left_mem_affineSpan_pair, mem_carrier]
  simp only [vsub_eq_sub, vadd_eq_add, sub_add_cancel, add_sub_cancel_left, Complex.real_smul]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := par_of_cr hd h
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    rw [← hr]
    simp only [cr_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- **B2.** For non-parallel lines, `meet L M` is the unique common point. -/
theorem meet_eq_iff {L M : Line} (h : cr M.d L.d ≠ 0) (z : ℂ) :
    (z ∈ L.carrier ∧ z ∈ M.carrier) ↔ z = meet L M := by
  constructor
  · rintro ⟨hL, hM⟩
    have hd : L.d ≠ 0 := by rintro e; apply h; rw [e, cr_def]; simp
    obtain ⟨r, hr⟩ := par_of_cr hd (mem_carrier.mp hL)
    rw [mem_carrier, show z - M.p = ((-1 : ℝ) : ℂ) * (M.p - L.p) + (r : ℂ) * L.d by
      rw [← hr]; push_cast; ring, cr_lin] at hM
    have hr' : r = cr M.d (M.p - L.p) / cr M.d L.d := by
      field_simp; linarith
    unfold meet; rw [← hr', ← hr]; ring
  · rintro rfl
    have h' : cr L.d M.d ≠ 0 := by rw [cr_comm]; exact neg_ne_zero.mpr h
    exact ⟨meet_mem_left L M, meet_mem_right L M h⟩

/-- The circumcentre denominator is `2 i` times the cross product. -/
lemma den_eq (a b c : ℂ) :
    conj (b - a) * (c - a) - (b - a) * conj (c - a) = 2 * I * (cr (b - a) (c - a) : ℂ) := by
  apply Complex.ext <;> simp [cr, Complex.mul_re, Complex.mul_im] <;> ring

/-- Three points are collinear iff the cross product of the edge vectors vanishes. -/
theorem collinear_iff_cr (a b c : ℂ) :
    Collinear ℝ ({a, b, c} : Set ℂ) ↔ cr (b - a) (c - a) = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert a _)]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨r₁, h₁⟩ := hv b (by simp)
    obtain ⟨r₂, h₂⟩ := hv c (by simp)
    rw [vadd_eq_add, Complex.real_smul] at h₁ h₂
    rw [show b - a = (r₁ : ℂ) * v by rw [h₁]; ring, show c - a = (r₂ : ℂ) * v by rw [h₂]; ring,
      cr_smul, cr_self, mul_zero]
  · intro h
    by_cases hb : b - a = 0
    · refine ⟨c - a, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by rw [sub_eq_zero] at hb; simp [hb]⟩
      · exact ⟨1, by simp⟩
    · obtain ⟨r, hr⟩ := par_of_cr hb h
      refine ⟨b - a, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨r, by rw [vadd_eq_add, Complex.real_smul, ← hr]; ring⟩

lemma ncol_iff_den (a b c : ℂ) :
    ¬ Collinear ℝ ({a, b, c} : Set ℂ) ↔ conj (b - a) * (c - a) - (b - a) * conj (c - a) ≠ 0 := by
  rw [collinear_iff_cr, den_eq]; simp [Complex.I_ne_zero]

/-- The circumcentre is equidistant from the three vertices (non-collinear case). -/
lemma circ_dist {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    dist b (circ a b c) = dist a (circ a b c) ∧ dist c (circ a b c) = dist a (circ a b c) := by
  have hD := (ncol_iff_den a b c).mp h
  have key : ∀ x : ℂ, x = 0 ∨ x = b - a ∨ x = c - a →
      Complex.normSq (x - (circ a b c - a)) = Complex.normSq (circ a b c - a) := by
    intro x hx
    apply Complex.ofReal_injective
    rw [normSq_cast, normSq_cast]
    unfold circ
    rw [add_sub_cancel_left, normSq_cast, normSq_cast]
    generalize b - a = u at hD hx ⊢
    generalize c - a = w at hD hx ⊢
    simp only [map_sub, map_mul, map_div₀, Complex.conj_conj]
    have hD' : conj u * w - conj w * u ≠ 0 := by intro e; apply hD; linear_combination e
    have hD'' : u * conj w - w * conj u ≠ 0 := by intro e; apply hD; linear_combination -e
    rcases hx with rfl | rfl | rfl
    · simp
    · generalize conj x = U at hD hD' hD'' ⊢; generalize conj w = W at hD hD' hD'' ⊢
      have h1 : x * W - U * w ≠ 0 := by
        intro e; apply hD; linear_combination -e
      field_simp; ring
    · generalize conj u = U at hD hD' hD'' ⊢; generalize conj x = W at hD hD' hD'' ⊢
      have h1 : x * U - W * u ≠ 0 := by
        intro e; apply hD; linear_combination e
      field_simp
      linear_combination (x * W * u * U - x * W ^ 2 * u) * mul_inv_cancel₀ h1
  have dn : ∀ p : ℂ, dist p (circ a b c) = Real.sqrt (Complex.normSq (p - a - (circ a b c - a))) := by
    intro p; rw [Complex.dist_eq, Complex.norm_def]; congr 2; ring
  refine ⟨?_, ?_⟩
  · rw [dn, dn, key _ (Or.inr (Or.inl rfl)), sub_self, key 0 (Or.inl rfl)]
  · rw [dn, dn, key _ (Or.inr (Or.inr rfl)), sub_self, key 0 (Or.inl rfl)]

/-- **B3.** `circ` is Mathlib's circumcentre of a non-collinear triangle. -/
theorem circ_eq_circumcenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    circ a b c = (⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 h⟩ :
      Affine.Triangle ℝ ℂ).circumcenter := by
  set t : Affine.Triangle ℝ ℂ := ⟨![a, b, c], affineIndependent_iff_not_collinear_set.2 h⟩
  have htop : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one, Complex.finrank_real_complex]
    simp
  obtain ⟨hb, hc⟩ := circ_dist h
  refine t.eq_circumcenter_of_dist_eq (by rw [htop]; exact AffineSubspace.mem_top _ _ _)
    (r := dist a (circ a b c)) (fun i => ?_)
  fin_cases i
  · rfl
  · exact hb
  · exact hc

/-- **B4.** `ortho` is Mathlib's orthocentre of a non-collinear triangle. -/
theorem ortho_eq_orthocenter {a b c : ℂ} (h : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) :
    ortho a b c = Affine.Triangle.orthocenter (⟨![a, b, c],
      affineIndependent_iff_not_collinear_set.2 h⟩ : Affine.Triangle ℝ ℂ) := by
  have e := Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub (⟨![a, b, c],
      affineIndependent_iff_not_collinear_set.2 h⟩ : Affine.Triangle ℝ ℂ)
  rw [← circ_eq_circumcenter h, Fin.sum_univ_three] at e
  simp only [vsub_eq_sub, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e
  unfold ortho
  linear_combination -e

/-- **B5.** `foot` is Mathlib's orthogonal projection onto the line `line[ℝ, p, p + d]`. -/
theorem foot_eq_orthogonalProjection (z : ℂ) (L : Line) (hd : L.d ≠ 0) :
    foot z L = (EuclideanGeometry.orthogonalProjection (line[ℝ, L.p, L.p + L.d]) z : ℂ) := by
  symm
  rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
  constructor
  · rw [← SetLike.mem_coe, ← carrier_eq_line L hd, mem_carrier]
    unfold foot
    rw [add_sub_cancel_left]
    simp only [cr_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  · rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right,
      Complex.inner, vsub_eq_sub, vsub_eq_sub, sub_add_cancel_left, map_neg, mul_neg,
      Complex.neg_re, neg_eq_zero]
    have hN' : L.d.re ^ 2 + L.d.im ^ 2 ≠ 0 := by
      rw [sq, sq, ← Complex.normSq_apply]; exact (Complex.normSq_pos.mpr hd).ne'
    unfold foot
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    field_simp; ring

/-- **B6.** Under `GenPos`, the four triangles are non-collinear and the six vertices are
pairwise distinct. -/
theorem genPos_triangles {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ¬ Collinear ℝ ({meet L₂ L₃, meet L₂ L₄, meet L₃ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₃, meet L₁ L₄, meet L₃ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₄, meet L₂ L₄} : Set ℂ) ∧
    ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₃, meet L₂ L₃} : Set ℂ) ∧
    List.Pairwise (· ≠ ·)
      [meet L₁ L₂, meet L₁ L₃, meet L₁ L₄, meet L₂ L₃, meet L₂ L₄, meet L₃ L₄] := by
  obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
    normal_coords h
  have hD := D_ne huw
  have hs := cne s0; have ht := cne t0; have hst := cne1 st
  have hs1 : (s : ℂ) - 1 ≠ 0 := by simpa using cne1 s1
  have ht1 : (t : ℂ) - 1 ≠ 0 := by simpa using cne1 t1
  have T1 : ¬ Collinear ℝ ({meet L₂ L₃, meet L₂ L₄, meet L₃ L₄} : Set ℂ) := by
    rw [ncol_iff_den, h23, h24, h34, add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    have e : conj ((t : ℂ) * w - w) * (nX u w s t - w) - ((t : ℂ) * w - w) * conj (nX u w s t - w)
        = -(s : ℂ) * (t - 1) ^ 2 / (s - t) * (conj w * u - conj u * w) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
      field_simp; ring
    rw [e]; simp [hs, hD, ht1, hst]
  have T2 : ¬ Collinear ℝ ({meet L₁ L₃, meet L₁ L₄, meet L₃ L₄} : Set ℂ) := by
    rw [ncol_iff_den, h13, h14, h34, add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    have e : conj ((s : ℂ) * u - u) * (nX u w s t - u) - ((s : ℂ) * u - u) * conj (nX u w s t - u)
        = -(t : ℂ) * (s - 1) ^ 2 / (s - t) * (conj w * u - conj u * w) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, conj_nX]; unfold nX
      field_simp; ring
    rw [e]; simp [ht, hD, hs1, hst]
  have T3 : ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₄, meet L₂ L₄} : Set ℂ) := by
    rw [ncol_iff_den, h12, h14, h24, add_sub_cancel_left, add_sub_cancel_left]
    have e : conj ((s : ℂ) * u) * ((t : ℂ) * w) - ((s : ℂ) * u) * conj ((t : ℂ) * w)
        = -(s : ℂ) * t * (conj w * u - conj u * w) := by
      simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e]; simp [hs, ht, hD]
  have T4 : ¬ Collinear ℝ ({meet L₁ L₂, meet L₁ L₃, meet L₂ L₃} : Set ℂ) := by
    rw [ncol_iff_den, h12, h13, h23, add_sub_cancel_left, add_sub_cancel_left]
    intro e; apply hD; linear_combination -e
  have dist3 : ∀ {a b c : ℂ}, ¬ Collinear ℝ ({a, b, c} : Set ℂ) → a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    intro a b c hc
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply hc
    · rw [Set.insert_eq_of_mem (Set.mem_insert _ _)]; exact collinear_pair ℝ _ _
    · rw [Set.pair_comm, Set.insert_eq_of_mem (Set.mem_insert _ _)]; exact collinear_pair ℝ _ _
    · rw [Set.insert_eq_of_mem (Set.mem_singleton _)]; exact collinear_pair ℝ _ _
  obtain ⟨m12a, m12b, m13a, m13b, m14a, m14b, m23a, m23b, m24a, m24b, m34a, m34b⟩ := h.mem
  have ne : ∀ {L : Line} {x y : ℂ}, x ∈ L.carrier → y ∉ L.carrier → x ≠ y :=
    fun hx hy hxy => hy (hxy ▸ hx)
  obtain ⟨a1, a2, a3⟩ := dist3 T1
  obtain ⟨b1, b2, b3⟩ := dist3 T2
  obtain ⟨c1, c2, c3⟩ := dist3 T3
  obtain ⟨d1, d2, d3⟩ := dist3 T4
  have e1 : meet L₁ L₂ ≠ meet L₃ L₄ := (ne m34a h.c123).symm
  have e2 : meet L₁ L₃ ≠ meet L₂ L₄ := (ne m24b h.c134).symm
  have e3 : meet L₁ L₄ ≠ meet L₂ L₃ := ne m14b h.c234
  refine ⟨T1, T2, T3, T4, ?_⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, ne_eq]
  exact ⟨⟨d1, c1, d2, c2, e1⟩, ⟨b1, d3, e2, b2⟩, ⟨e3, c3, b3⟩, ⟨a1, a2⟩, ⟨a3, by simp⟩⟩

/-- **N1.** `pw z P Q` is Mathlib's power of `z` w.r.t. the circle on diameter `P Q`. -/
theorem pw_eq_power (z P Q : ℂ) :
    pw z P Q = (⟨(P + Q) / 2, dist P Q / 2⟩ : EuclideanGeometry.Sphere ℂ).power z := by
  rw [EuclideanGeometry.Sphere.power, pw, Complex.dist_eq, Complex.dist_eq]
  ring

/-- The circle on diameter `P Q`. -/
noncomputable def diamCircle (P Q : ℂ) : EuclideanGeometry.Sphere ℂ := ⟨(P + Q) / 2, dist P Q / 2⟩

/-- **N2.** Bodenmiller with Mathlib's `Sphere.power`: every orthocentre has equal power w.r.t.
the three circles on the diagonals, and the three centres (diagonal midpoints) are pairwise
distinct, so the coaxality statement is not vacuous. -/
theorem bodenmiller_coaxal {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    (∀ H ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      (diamCircle (meet L₁ L₂) (meet L₃ L₄)).power H =
        (diamCircle (meet L₁ L₃) (meet L₂ L₄)).power H ∧
      (diamCircle (meet L₁ L₂) (meet L₃ L₄)).power H =
        (diamCircle (meet L₁ L₄) (meet L₂ L₃)).power H) ∧
    (diamCircle (meet L₁ L₂) (meet L₃ L₄)).center ≠ (diamCircle (meet L₁ L₃) (meet L₂ L₄)).center ∧
    (diamCircle (meet L₁ L₂) (meet L₃ L₄)).center ≠ (diamCircle (meet L₁ L₄) (meet L₂ L₃)).center ∧
    (diamCircle (meet L₁ L₃) (meet L₂ L₄)).center ≠ (diamCircle (meet L₁ L₄) (meet L₂ L₃)).center := by
  refine ⟨fun H hH => ?_, diag_midpoints_ne h, ?_, ?_⟩
  · simp only [diamCircle, ← pw_eq_power]; exact bodenmiller h H hH
  · obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
      normal_coords h
    simp only [diamCircle]
    rw [h12, h14, h23, h34]
    have hst := cne1 st
    intro e
    have e' : ((s * (s - 1) / (s - t) : ℝ) : ℂ) * u + ((s * (1 - t) / (s - t) : ℝ) : ℂ) * w = 0 := by
      have : (s : ℂ) * u + w - nX u w s t = 0 := by linear_combination -2 * e
      unfold nX at this; push_cast; field_simp at this ⊢; linear_combination this
    have := (indep huw e').1
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact s0 h0
      · exact s1 (by linarith)
    · exact st (by linarith)
  · obtain ⟨O, u, w, s, t, -, -, h12, h13, h23, h14, h24, h34, huw, s0, s1, t0, t1, st, -⟩ :=
      normal_coords h
    simp only [diamCircle]
    rw [h13, h14, h23, h24]
    intro e
    have := (indep huw (x := 1 - s) (y := t - 1) (by push_cast; linear_combination 2 * e)).1
    exact s1 (by linarith)

/-- **N3.** The perpendicularity condition `Re (a * conj b) = 0` is Mathlib's real inner
product on `ℂ` vanishing. -/
theorem perp_iff_inner (a b : ℂ) : (a * conj b).re = 0 ↔ inner ℝ a b = 0 := by
  rw [Complex.inner, ← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

/-- `orthocentre_line_perp` restated with Mathlib's inner product. -/
theorem orthocentre_line_perp_inner {L₁ L₂ L₃ L₄ : Line} (h : GenPos L₁ L₂ L₃ L₄) :
    ∀ H₁ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
    ∀ H₂ ∈ ({ortho (meet L₂ L₃) (meet L₂ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₃) (meet L₁ L₄) (meet L₃ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₄) (meet L₂ L₄),
      ortho (meet L₁ L₂) (meet L₁ L₃) (meet L₂ L₃)} : Set ℂ),
      inner ℝ ((meet L₁ L₃ + meet L₂ L₄) / 2 - (meet L₁ L₂ + meet L₃ L₄) / 2) (H₂ - H₁) = 0 :=
  fun H₁ h₁ H₂ h₂ => (perp_iff_inner _ _).mp (orthocentre_line_perp h H₁ h₁ H₂ h₂)

/-- The Mathlib line of a `Line`. -/
noncomputable def Line.toAffine (L : Line) : AffineSubspace ℝ ℂ := line[ℝ, L.p, L.p + L.d]

/-- Two lines with nonzero directions are parallel (in Mathlib's sense) iff `cr` vanishes. -/
theorem parallel_iff_cr {L M : Line} (hL : L.d ≠ 0) (hM : M.d ≠ 0) :
    L.toAffine.Parallel M.toAffine ↔ cr L.d M.d = 0 := by
  rw [Line.toAffine, Line.toAffine, AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq,
    vectorSpan_pair, vectorSpan_pair, vsub_eq_sub, vsub_eq_sub, sub_add_cancel_left,
    sub_add_cancel_left, Submodule.span_singleton_eq_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    rw [Units.smul_def, Complex.real_smul] at hz
    rw [show M.d = ((z : ℝ) : ℂ) * L.d by linear_combination hz]
    simp only [cr_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  · intro h
    obtain ⟨r, hr⟩ := par_of_cr hL h
    have r0 : r ≠ 0 := by rintro rfl; apply hM; simpa using hr
    exact ⟨Units.mk0 r r0, by rw [Units.smul_def, Units.val_mk0, Complex.real_smul, hr]; ring⟩

/-- Under nonzero directions and non-parallelism, `meet L M ∉ N.carrier` iff the three lines
have no common point. -/
lemma not_concurrent_iff {L M N : Line} (hN : N.d ≠ 0) (h : cr M.d L.d ≠ 0) :
    meet L M ∉ N.carrier ↔ ¬ ∃ z, z ∈ L.toAffine ∧ z ∈ M.toAffine ∧ z ∈ N.toAffine := by
  have hL : L.d ≠ 0 := by rintro e; apply h; rw [e, cr_def]; simp
  have hM : M.d ≠ 0 := by rintro e; apply h; rw [e, cr_def]; simp
  simp only [Line.toAffine, ← SetLike.mem_coe, ← carrier_eq_line _ hL, ← carrier_eq_line _ hM,
    ← carrier_eq_line _ hN]
  constructor
  · rintro hn ⟨z, z1, z2, z3⟩
    exact hn ((meet_eq_iff h z).mp ⟨z1, z2⟩ ▸ z3)
  · rintro hn hm
    exact hn ⟨_, meet_mem_left L M, ((meet_eq_iff h _).mpr rfl).2, hm⟩

/-- **B7.** `GenPos` in Mathlib terms: nonzero directions, pairwise non-parallel lines
(`AffineSubspace.Parallel`), and no three of the lines through a common point. -/
theorem genPos_iff {L₁ L₂ L₃ L₄ : Line} :
    GenPos L₁ L₂ L₃ L₄ ↔
      (L₁.d ≠ 0 ∧ L₂.d ≠ 0 ∧ L₃.d ≠ 0 ∧ L₄.d ≠ 0) ∧
      (¬ L₁.toAffine.Parallel L₂.toAffine ∧ ¬ L₁.toAffine.Parallel L₃.toAffine ∧
        ¬ L₁.toAffine.Parallel L₄.toAffine ∧ ¬ L₂.toAffine.Parallel L₃.toAffine ∧
        ¬ L₂.toAffine.Parallel L₄.toAffine ∧ ¬ L₃.toAffine.Parallel L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₂.toAffine ∧ z ∈ L₃.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₂.toAffine ∧ z ∈ L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₁.toAffine ∧ z ∈ L₃.toAffine ∧ z ∈ L₄.toAffine) ∧
      (¬ ∃ z, z ∈ L₂.toAffine ∧ z ∈ L₃.toAffine ∧ z ∈ L₄.toAffine) := by
  have r : ∀ {a b : ℂ}, cr a b ≠ 0 → cr b a ≠ 0 := fun hh => by
    rw [cr_comm]; exact neg_ne_zero.mpr hh
  constructor
  · intro h
    refine ⟨⟨h.d₁, h.d₂, h.d₃, h.d₄⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [parallel_iff_cr h.d₁ h.d₂]; exact h.p12
    · rw [parallel_iff_cr h.d₁ h.d₃]; exact h.p13
    · rw [parallel_iff_cr h.d₁ h.d₄]; exact h.p14
    · rw [parallel_iff_cr h.d₂ h.d₃]; exact h.p23
    · rw [parallel_iff_cr h.d₂ h.d₄]; exact h.p24
    · rw [parallel_iff_cr h.d₃ h.d₄]; exact h.p34
    · exact (not_concurrent_iff h.d₃ (r h.p12)).mp h.c123
    · exact (not_concurrent_iff h.d₄ (r h.p12)).mp h.c124
    · exact (not_concurrent_iff h.d₄ (r h.p13)).mp h.c134
    · exact (not_concurrent_iff h.d₄ (r h.p23)).mp h.c234
  · rintro ⟨⟨d₁, d₂, d₃, d₄⟩, ⟨q12, q13, q14, q23, q24, q34⟩, c123, c124, c134, c234⟩
    rw [parallel_iff_cr d₁ d₂] at q12; rw [parallel_iff_cr d₁ d₃] at q13
    rw [parallel_iff_cr d₁ d₄] at q14; rw [parallel_iff_cr d₂ d₃] at q23
    rw [parallel_iff_cr d₂ d₄] at q24; rw [parallel_iff_cr d₃ d₄] at q34
    exact ⟨d₁, d₂, d₃, d₄, q12, q13, q14, q23, q24, q34,
      (not_concurrent_iff d₃ (r q12)).mpr c123, (not_concurrent_iff d₄ (r q12)).mpr c124,
      (not_concurrent_iff d₄ (r q13)).mpr c134, (not_concurrent_iff d₄ (r q23)).mpr c234⟩

end QuadNewton
