import Mathlib

theorem algebra_303316 (a : ℕ → ℝ) (ha1 : a 1 = 1) (han : ∀ n, a (n + 1) = a n + 1 / a n) :
    14 < a 100 ∧ a 100 < 18 := by
  have ha2 : a 1 = a 0 + 1 / a 0 := han 0
  have ha0' : a 0 ≠ 0 := by
    by_contra h0
    have h3 : a 0 = (0 : ℝ) := by linarith 
    have h4 : a 1 = (0 : ℝ) := by
      rw [show a 1 = a 0 + 1 / a 0 by linarith [han 0]]
      rw [h3]
      norm_num 
    linarith [ha1, h4]
  
  have h1 : a 1 = a 0 + 1 / a 0 := han 0
  rw [ha1] at h1

  have h6 : a 0 ^ 2 - a 0 + 1 = (0 : ℝ) := by
    have h_eq : a 0 + 1 / a 0 = (1 : ℝ) := by linarith [h1] 
    have h7 : a 0 ^ 2 - a 0 + 1 = (0 : ℝ) := by
      have h8 : a 0 * (a 0 + 1 / a 0) = a 0 * (1 : ℝ) := by 
        rw [h_eq]
      have h9 : a 0 * (a 0 + 1 / a 0) = a 0 ^ 2 + 1 := by 
        field_simp [show a 0 ≠ 0 by exact ha0']
        <;> nlinarith 
      have h10 : a 0 * (1 : ℝ) = a 0 := by ring
      nlinarith [h8, h9, h10]
    exact h7
  
  have h8 : (a 0 - 1 / 2) ^ 2 = -3 / 4 := by
    nlinarith [sq_nonneg (a 0 - 1 / 2)]

  have h9 : (a 0 - 1 / 2) ^ 2 < (0 : ℝ) := by 
    nlinarith [h8]

  linarith [sq_nonneg (a 0 - 1 / 2), h9]