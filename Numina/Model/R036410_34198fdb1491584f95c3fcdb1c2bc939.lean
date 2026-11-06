import Mathlib

theorem number_theory_146243 (x : ℕ → ℤ)
    (hx1 : x 1 = 3)
    (hxn : ∀ n, x (n + 1) = ⌊Real.sqrt 2 * x n⌋) :
    {n | ∃ d, x n + d = x (n + 1) ∧ x (n + 1) + d = x (n + 2)} =
    {1, 3} := by 
  have h1 := hxn 0
  rw [show x 1 = 3 by linarith [hx1]] at h1 
  have h2 : (3 : ℤ) = ⌊Real.sqrt 2 * (x 0 : ℝ)⌋ := by
    exact_mod_cast h1
  have h3 : 3 ≤ Real.sqrt 2 * (x 0 : ℝ) := by
    have h4 : (3 : ℝ) ≤ Real.sqrt 2 * (x 0 : ℝ) := by
      have h4 : (⌊Real.sqrt 2 * (x 0 : ℝ)⌋ : ℝ) ≤ Real.sqrt 2 * (x 0 : ℝ) := by
        exact Int.floor_le (Real.sqrt 2 * (x 0 : ℝ))
      have h5 : (⌊Real.sqrt 2 * (x 0 : ℝ)⌋ : ℝ) = (3 : ℝ) := by 
        exact_mod_cast show ⌊Real.sqrt 2 * (x 0 : ℝ)⌋ = (3 : ℤ) by 
          omega
      nlinarith
    linarith
  have h4 : Real.sqrt 2 * (x 0 : ℝ) < (4 : ℝ) := by
    have h5 : Real.sqrt 2 * (x 0 : ℝ) < (⌊Real.sqrt 2 * (x 0 : ℝ)⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one (Real.sqrt 2 * (x 0 : ℝ))
    have h6 : (⌊Real.sqrt 2 * (x 0 : ℝ)⌋ + 1 : ℝ) = (4 : ℝ) := by
      have h7 : ⌊Real.sqrt 2 * (x 0 : ℝ)⌋ = (3 : ℤ) := by
        omega
      rw [show ⌊Real.sqrt 2 * (x 0 : ℝ)⌋ = (3 : ℤ) by omega] 
      norm_num
    linarith
  by_cases h10 : x 0 ≤ (2 : ℤ)
  · -- Case x 0 ≤ 2
    have h5 : (x 0 : ℝ) ≤ (2 : ℝ) := by exact_mod_cast h10
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  · -- Case x 0 > 2
    have h6 : x 0 ≥ 3 := by 
      omega
    have h7 : (x 0 : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h6
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]