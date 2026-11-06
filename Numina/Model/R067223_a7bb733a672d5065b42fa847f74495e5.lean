import Mathlib

theorem algebra_173630 (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / (n ^ 2 + 3 * n + 2)) :
    ∀ m, ∑ i in Finset.Icc 0 m, a i < 1 := by
  intro m
  have h1 : ∀ m : ℕ, ∑ i in Finset.Icc 0 m, a i = (m + 1) / (m + 2 : ℝ) := by
    intro m
    induction m with
    | zero =>
      norm_num [Finset.sum_singleton, ha]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      simp [ha]
      field_simp
      ring
  have h2 : ∑ i in Finset.Icc 0 m, a i = (m + 1 : ℝ) / (m + 2 : ℝ) := h1 m
  rw [h2]
  have h4 : (m + 1 : ℝ) / (m + 2 : ℝ) < 1 := by
    have h4 : (m + 2 : ℝ) > 0 := by
      have hm : (m : ℝ) ≥ 0 := by
        exact_mod_cast (show (m : ℕ) ≥ 0 by omega)
      nlinarith
    have h5 : (m + 1 : ℝ) < (m + 2 : ℝ) := by
      nlinarith
    have h6 : (m + 1 : ℝ) / (m + 2 : ℝ) < (1 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  linarith [h4]