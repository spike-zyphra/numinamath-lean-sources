import Mathlib

open Complex Real Polynomial

/- Let $g(x)$ be a polynomial with leading coefficient $1$,
  whose three roots are the reciprocals of the three roots of $f(x)=x^3+ax^2+bx+c$,
  where $1 < a < b < c$.
  What is $g(1)$ in terms of $a, b$ and $c$? -/

theorem AMC_94355
    (a b c : ℝ)
    (f g : Polynomial ℝ)
    (hf : f = X ^ 3 + C a * X ^ 2 + C b * X + C c)
    (hg : (g.map ofRealHom).roots = (f.map ofRealHom).roots.map (1 / ·))
    (hg_lead : g.leadingCoeff = 1)
    (h : 1 < a ∧ a < b ∧ b < c) :
    g.eval 1 = (1 + a + b + c) / c := by

  -- To begin, we prove several auxiliary lemmas. Here, we prove that f is monic
  have hf_lead : f.leadingCoeff = 1 := by
    change f.Monic
    rw [hf, add_assoc (X ^ 3), add_assoc]
    apply Monic.add_of_left
    · exact monic_X_pow 3
    · rw [degree_pow, degree_X]
      exact degree_quadratic_lt

  -- And also that f has 3 roots, as deg(f) = 3 and splits in ℂ[x] as ℂ is algebraically closed
  have hf_degree : (map ofRealHom f).roots.card = 3 := by
    rw [← natDegree_eq_card_roots]
    · rw [hf]
      compute_degree!
    · exact IsAlgClosed.splits_codomain f
  -- Name the roots x, y, z.
  obtain ⟨x, y, z, hf_roots⟩ := Multiset.card_eq_three.mp hf_degree

  -- Then, f(X) = (X - x)(X - y)(X - z)
  have hf_eq : f.map ofRealHom = (X - C x) * (X - C y) * (X - C z) := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := f.map ofRealHom) ?_
    · rw [leadingCoeff_map, hf_lead, ofRealHom_eq_coe, ofReal_one, map_one, one_mul] at this
      simp [hf_roots, ← mul_assoc] at this
      tauto
    · rw [hf_degree, eq_comm]
      simp only [hf, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_mul, map_C,
        ofRealHom_eq_coe, natDegree_add_C]
      compute_degree!

  -- By the information given, the roots of g are 1 / x, 1 / y, 1 / z.
  have hg_roots : (g.map ofRealHom).roots = {1 / x, 1 / y, 1 / z} := by
    rw [hg, hf_roots]
    rfl

  -- Hence, g(X) = (X - 1 / x)(X - 1 / y)(X - 1 / z)
  have hg_eq : g.map ofRealHom = (X - C (1 / x)) * (X - C (1 / y)) * (X - C (1 / z)) := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g.map ofRealHom) ?_
    · rw [leadingCoeff_map, hg_lead, ofRealHom_eq_coe, ofReal_one, map_one, one_mul] at this
      simp [hg_roots, ← mul_assoc] at this
      simp_rw [inv_eq_one_div] at this
      rw [← this]
    · rw [natDegree_eq_card_roots (p := g.map ofRealHom) (i := RingHom.id ℂ) ?_]
      · simp
      · exact IsAlgClosed.splits (map ofRealHom g)

  -- We can also prove that x, y, z are nonzero, as otherwise f(0) = 0 but 1 < c.
  obtain ⟨hx, hy, hz⟩ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
    use ?_, ?_, ?_
    all_goals
      rintro rfl
      have h_zero : 0 ∈ (f.map ofRealHom).roots := by
        rw [hf_roots]
        simp
      have : (f.map ofRealHom).eval 0 = 0 := by
        apply (mem_roots ?_).mp h_zero
        intro hf
        simp [hf, X_sub_C_ne_zero] at hf_eq
      simp [hf] at this
      linarith [h.left.trans (h.right.left.trans h.right.right)]

  -- Now, we look at relationship between f(1) and g(1).
  -- We prove that g(1) = f(1) / (-xyz) = f(1) / f(0).
  have hf_eval : (f.map ofRealHom).eval 1 = (1 - x) * (1 - y) * (1 - z) := by
    rw [hf_eq]
    simp
  have hg_eval : (g.map ofRealHom).eval 1 = (1 - 1 / x) * (1 - 1 / y) * (1 - 1 / z) := by
    rw [hg_eq]
    simp
  have aux : (g.map ofRealHom).eval 1 = (-(x * y * z))⁻¹ * (f.map ofRealHom).eval 1 := calc
    (g.map ofRealHom).eval 1 = (1 - 1 / x) * (1 - 1 / y) * (1 - 1 / z) := hg_eval
    _ = (x⁻¹ * (x - 1)) * (y⁻¹ * (y - 1)) * (z⁻¹ * (z - 1)) := by
      congr 2
      · rw [eq_inv_mul_iff_mul_eq₀ hx, mul_sub, mul_one, mul_one_div, div_self hx]
      · rw [eq_inv_mul_iff_mul_eq₀ hy, mul_sub, mul_one, mul_one_div, div_self hy]
      · rw [eq_inv_mul_iff_mul_eq₀ hz, mul_sub, mul_one, mul_one_div, div_self hz]
    _ = _ := by
      rw [hf_eval]
      ring_nf

  have h_prod : -(x * y * z) = c := by
    apply_fun fun p ↦ p.eval 0 at hf_eq
    simp at hf_eq
    rw [← coeff_zero_eq_eval_zero] at hf_eq
    rw [← hf_eq]
    simp [hf]

  have hf_eval' : (f.map ofRealHom).eval 1 = 1 + a + b + c := by
    simp [hf]

  -- Since f(1) = 1 + a + b + c and f(0) = c, we obtain g(1) = (1 + a + b + c) / c.
  rw [h_prod, hf_eval'] at aux
  rw [eval_one_map, ofRealHom_eq_coe] at aux
  norm_cast at aux
  rwa [inv_eq_one_div, mul_comm, mul_one_div] at aux