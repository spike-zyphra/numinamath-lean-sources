import Mathlib

theorem algebra_325478 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (h : ∑ i : Fin n, (x i)^2 = 1) (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : Fin n → ℤ,
      (∀ i : Fin n, |a i| ≤ k - 1) ∧
      |∑ i : Fin n, a i * x i| ≤ ((k - 1) * Real.sqrt n) / (k^n - 1) := by
  use fun _ => 0
  constructor
  · -- Show that for all i, the absolute value of 0 is ≤ k-1
    intro i
    simp
    all_goals omega
  · -- Show that the absolute value of the sum is ≤ ((k - 1) * Real.sqrt n) / (k^n - 1)
    simp
    all_goals
      have h1 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hk
      have h2 : (k ^ n : ℝ) ≥ (2 : ℝ) := by
        have h3 : (k ^ n : ℝ) ≥ (2 : ℝ) := by
          have h4 : k ^ n ≥ 2 ^ n := by
            apply Nat.pow_le_pow_of_le_left
            all_goals
              linarith
          have h5 : 2 ^ n ≥ 2 := by
            have h6 : 2 ^ n ≥ 2 ^ 1 := by
              apply Nat.pow_le_pow_of_le_right
              all_goals linarith
            have h7 : 2 ^ 1 = 2 := by norm_num
            linarith [h7]
          have h8 : (k ^ n : ℝ) ≥ (2 : ℝ) := by
            have h9 : (k ^ n : ℝ) ≥ (2 ^ n : ℝ) := by exact_mod_cast h4
            have h10 : (2 ^ n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h5
            linarith
          linarith
        linarith
      have h3 : (Real.sqrt n) ≥ (0 : ℝ) := by
        apply Real.sqrt_nonneg
      have h4 : (k ^ n : ℝ) - 1 > 0 := by
        have h5 : (k ^ n : ℝ) ≥ (2 : ℝ) := h2
        linarith
      have h5 : (k - 1 : ℝ) ≥ 0 := by
        have hk2 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hk
        have hk1 : (k : ℝ) - 1 ≥ 1 := by linarith
        linarith
      have h6 : ((k - 1 : ℝ) * Real.sqrt n) / ((k ^ n : ℝ) - 1) ≥ 0 := by
        apply div_nonneg
        · -- Numerator is non-negative
          nlinarith [Real.sqrt_nonneg n]
        · -- Denominator is non-negative
          nlinarith
      linarith