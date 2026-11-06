import Mathlib

open Real

theorem inequalities_159225 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (h : ∏ i, a i = 1) :
    ∏ i, (1 + a i) ≥ 2 ^ n := by
  have h1 : ∀ i, 1 + a i ≥ 2 * Real.sqrt (a i) := by
    intro i
    have h2 : a i > 0 := ha i 
    have h3 : Real.sqrt (a i) > 0 := by 
      apply Real.sqrt_pos.mpr 
      linarith 
    have h4 : Real.sqrt (a i) ^ 2 = a i := by 
      rw [Real.sq_sqrt]
      linarith 
    nlinarith [sq_nonneg (Real.sqrt (a i) - 1), Real.sqrt_nonneg (a i)]
  have h2 : ∏ i, (1 + a i) ≥ ∏ i, (2 * Real.sqrt (a i)) := by 
    apply Finset.prod_le_prod
    · intro i hi 
      have ha1 : 0 < 2 * Real.sqrt (a i) := by 
        have h2 : a i > 0 := ha i
        have h3 : Real.sqrt (a i) > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith 
        nlinarith [Real.sqrt_nonneg (a i)]
      positivity 
    · intro i hi 
      have h11 : 1 + a i ≥ 2 * Real.sqrt (a i) := h1 i 
      exact h11 
  have h3 : ∏ i, (2 * Real.sqrt (a i)) = 2 ^ n * ∏ i, Real.sqrt (a i) := by 
    calc 
      ∏ i, (2 * Real.sqrt (a i)) = ∏ i, (2 * (Real.sqrt (a i) )) := by rfl 
      _ = (∏ i, (2 : ℝ)) * (∏ i, Real.sqrt (a i)) := by 
        rw [Finset.prod_mul_distrib]
      _ = 2 ^ n * (∏ i, Real.sqrt (a i)) := by 
        simp [Finset.prod_const, hn]
  have h4 : ∏ i : Fin n, Real.sqrt (a i) = 1 := by 
    have h6 : ∀ i : Fin n, Real.sqrt (a i) = (a i) ^ (1 / 2 : ℝ) := by 
      intro i 
      rw [Real.sqrt_eq_rpow]
    have h7 : ∏ i : Fin n, Real.sqrt (a i) = ∏ i : Fin n, (a i) ^ (1 / 2 : ℝ) := by 
      congr 
      funext i 
      exact h6 i 
    have h8 : ∏ i : Fin n, (a i) ^ (1 / 2 : ℝ) = (∏ i : Fin n, (a i)) ^ (1 / 2 : ℝ) := by 
      rw [← Real.finset_prod_rpow]
      intro i hi
      have h10 : 0 ≤ a i := by 
        have h20 : a i > 0 := ha i 
        linarith 
      exact h10 
    rw [h7, h8, h]
    all_goals norm_num
  have h5 : ∏ i, (1 + a i) ≥ 2 ^ n * ∏ i, Real.sqrt (a i) := by 
    calc 
      ∏ i, (1 + a i) ≥ ∏ i, (2 * Real.sqrt (a i)) := h2
      _ = 2 ^ n * ∏ i, Real.sqrt (a i) := h3 
  have h6 : 2 ^ n * ∏ i : Fin n, Real.sqrt (a i) = 2 ^ n := by 
    rw [h4]
    all_goals norm_num 
  linarith [h5, h6]