import Mathlib

theorem algebra_318285 {k : ℝ} (hk : k = ∫ x in (0)..Real.pi, (Real.sin x - Real.cos x)) (a : ℕ → ℝ)
    (h : ∀ x, (1 - k * x) ^ 8 = ∑ i in Finset.range 9, a i * x ^ i) :
    ∑ i in Finset.Icc 1 8, a i = 0 := by
  have sk : k = 2 := by 
    rw [hk]
    norm_num [Real.sin_pi, Real.cos_pi]
  have eq1 := h 1
  rw [sk] at eq1
  have eq2 := h 0
  rw [sk] at eq2
  simp [Finset.sum_range_succ] at eq1 eq2
  norm_num at eq1 eq2
  have eq3 : a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 = 0 := by
    linarith
  norm_num [Finset.sum_Icc_succ_top] at *
  linarith [eq3]