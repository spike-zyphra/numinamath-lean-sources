import Mathlib

theorem algebra_601109 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (h : ∑ i : Fin n, (x i)^2 = 1) (k : ℕ) (hk : 3 ≤ k) :
    ∃ a : Fin n → ℤ,
      (∀ i : Fin n, |a i| ≤ k - 1) ∧
      |∑ i : Fin n, a i * x i| ≤ ((k - 1) * Real.sqrt n) / (k^n - 1) := by 
  use (λ _ : Fin n => (0 : ℤ))
  constructor 
  · -- Show that ∀ i : Fin n, |0| ≤ k - 1 
    intro i 
    simp 
    all_goals 
    omega 
  · -- Show that |∑ i : Fin n, 0 * x i| ≤ (k - 1) * Real.sqrt n / (k^n - 1) 
    have h1 : |∑ i : Fin n, (0 : ℤ) * x i| = 0 := by 
      simp 
    rw [h1] 
    have hk1 : k ≥ 3 := by omega 
    have h2 : k - 1 ≥ 2 := by 
      omega 
    have hn1 : n > 0 := by exact_mod_cast hn 
    have hn2 : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 by omega) 
    have h3 : (k : ℝ) ≥ 3 := by exact_mod_cast (show k ≥ 3 by omega) 
    have h4 : (k : ℝ) ^ (n : ℕ) ≥ (3 : ℝ) := by
      have h1 : k ≥ 3 := by omega 
      have h11 : (k : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h1
      have hn1 : n ≥ 1 := by omega 
      have hx1 : (k : ℝ) ^ n ≥ (3 : ℝ) ^ n := by 
        apply pow_le_pow_left 
        all_goals 
        linarith 
      have hx2 : (3 : ℝ) ^ n ≥ (3 : ℝ) := by
        have hn1 : n ≥ 1 := by 
          omega 
        have h9 : (3 : ℝ) ^n ≥ (3 : ℝ)^1 := by 
          apply pow_le_pow_right 
          all_goals linarith 
        have h10 : (3 : ℝ)^1 = (3 : ℝ) := by 
          norm_num 
        rw [h10] at h9 
        linarith 
      nlinarith [hx1, hx2] 
    have h6 : (k : ℝ) ^ n ≥ (3 : ℝ) := h4 
    have h10 : Real.sqrt (n : ℝ) > 0 := by 
      apply Real.sqrt_pos.2 
      linarith 
    have hx4 : (k : ℝ) ^ n - 1 > 0 := by 
      nlinarith 
    have hx2 : (k : ℝ) - 1 ≥ 2 := by 
      have h1 : k ≥ 3 := by omega 
      have h2 : k ≥ 3 := by linarith 
      have h3 : (k : ℝ) ≥ (3 : ℝ) := by 
        exact_mod_cast (show k ≥ 3 by omega) 
      nlinarith 
    have h17 : (k - 1 : ℝ) * Real.sqrt (n : ℝ) / (k^n - 1) ≥ (0 : ℝ) := by 
      apply div_nonneg 
      · -- Show (k - 1 : ℝ) * Real.sqrt (n : ℝ) ≥ 0 
        positivity 
      all_goals -- Show denominator ≥ 0 
        positivity 
    linarith