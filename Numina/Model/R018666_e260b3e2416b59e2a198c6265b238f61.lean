import Mathlib

theorem inequalities_307777 (m n : ℝ) (h₀ : 0 < m) (h₁ : 0 < n) (h₂ : m + n = 1) :
    (1 + m) ^ n * (1 + n) ^ m ≤ 1 + 2 * m * n := by
  have h3 : n = 1 - m := by linarith
  rw [show n = 1 - m by linarith]
  have h4 : (1 + m : ℝ) ^ (1 - m) * (1 + (1 - m) : ℝ) ^ (m) ≤ (1 - m) * (1 + m) + m * (1 + (1 - m)) := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      nlinarith
    all_goals 
      nlinarith
  have h5 : (1 - m : ℝ) * (1 + m) + m * (1 + (1 - m) : ℝ) = 1 + 2 * m * (1 - m) := by
    ring
  have h8 : (1 + m : ℝ) ^ (1 - m) * (1 + (1 - m) : ℝ) ^ (m : ℝ) ≤ (1 + 2 * m * (1 - m) : ℝ) := by
    linarith [h4, h5]
  have h9 : (1 + 2 * m * (1 - m) : ℝ) = (1 + 2 * m * n : ℝ) := by 
    rw [show (1 - m : ℝ) = n by nlinarith]
    all_goals ring_nf
    <;> nlinarith [h₂]
  nlinarith [h8, h9]
  all_goals
    try { nlinarith }
    all_goals
      linarith