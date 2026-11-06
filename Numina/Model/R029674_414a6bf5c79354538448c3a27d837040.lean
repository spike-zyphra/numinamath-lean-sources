import Mathlib

theorem algebra_230903 (a : ℕ → ℝ) (h₀ : 0 < a 1) (h₁ : a 1 < 1)
    (h₂ : 1 < a 2) (h₃ : a 2 < 2) (h₄ : 2 < a 3) (h₅ : a 3 < 3)
    (h₆ : ∃ r, ∀ n, a n = a 1 * r ^ (n - 1)) :
    2 * Real.sqrt 2 < a 4 ∧ a 4 < 9 := by
  rcases h₆ with ⟨r, hr⟩
  have ha2 : a 2 = a 1 * r ^ 1 := hr 2
  have ha3 : a 3 = a 1 * r ^ 2 := hr 3
  have ha4 : a 4 = a 1 * r ^ 3 := hr 4
  have eq_a2 : a 2 = a 1 * r := by
    rw [ha2]
    <;> ring
  have eq_a3 : a 3 = a 1 * r ^ 2 := by 
    rw [ha3]
    <;> ring
  have eq_a4 : a 4 = a 1 * r ^ 3 := by 
    rw [ha4]
    <;> ring
  have h7 : 1 < a 1 * r := by
    nlinarith [h₂, eq_a2]
  have h8 : a 1 * r < 2 := by
    nlinarith [h₃, eq_a2]
  have h9 : 2 < a 1 * r ^ 2 := by
    nlinarith [h₄, eq_a3]
  have h10 : a 1 * r ^ 2 < 3 := by
    nlinarith [h₅, eq_a3]
  have h11 : a 4 = a 1 * r ^ 3 := eq_a4
  have h14 : a 1 * r ^ 3 > 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (a 1 * r - Real.sqrt 2), sq_nonneg (r - Real.sqrt 2), 
      sq_nonneg (a 1 * r ^ 2 - 2), sq_nonneg (a 1 * r - 1), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
      h7, h8, h9, h10, mul_pos (show 0 < a 1 by linarith) (show 0 < r by nlinarith)]
  have h15 : a 1 * r ^ 3 < 9 := by
    nlinarith [sq_nonneg (a 1 * r - 1), sq_nonneg (r - 2), sq_nonneg (a 1 * r ^ 2 - 3), sq_nonneg (a 1 * r - 2), 
      h7, h8, h9, h10, mul_pos (show 0 < a 1 by linarith) (show 0 < r by nlinarith)]
  constructor
  · -- Prove the lower bound: 2 * Real.sqrt 2 < a 4
    nlinarith [h11, h14]
  · -- Prove the upper bound: a 4 < 9
    nlinarith [h11, h15]