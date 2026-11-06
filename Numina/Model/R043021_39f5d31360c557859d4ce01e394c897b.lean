import Mathlib

theorem algebra_312378 {a : ℝ} (ha : a < 0) (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 + 2 * a * x1 + a^2 / 2 = 0 ∧ x2^2 + 2 * a * x2 + a^2 / 2 = 0 ∧
    (x2 - x1)^2 = (x2 + x1)^2 / 3) :
    a = -Real.sqrt 6 := by 
  rcases h with ⟨x1, x2, hx12, h1, h2, h3⟩
  have h5 : x1 + x2 = -2 * a := by
    have eq1 : (x1 - x2) * (x1 + x2 + 2 * a) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp eq1) with h4 h5
    · -- Case $x1 - x2 = 0$ is impossible since $x1 \neq x2$.
      exfalso
      apply hx12
      linarith 
    · -- Now $x1 + x2 + 2 * a = 0$ implies $x1 + x2 = -2 * a$.
      linarith 
  have h6 : (x1 - x2) ^ 2 = 4 * a^2 / 3 := by
    have eq2 : x2 + x1 = -2 * a := by linarith 
    have eq3 : (x2 - x1) ^ 2 = (4 * a^2) / 3 := by 
      rw [eq2] at h3 
      nlinarith 
    have eq4 : (x1 - x2) ^ 2 = (x2 - x1) ^ 2 := by ring 
    nlinarith [eq4, eq3]
  have h8 : a^2 = 6 := by 
    nlinarith [sq_pos_of_neg ha, sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by 
      by_contra h'
      apply hx12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2) ]
  have h9 : a = -Real.sqrt 6 := by 
    have h10 : a < 0 := ha 
    have h11 : a^2 = 6 := h8 
    have h12 : a = -Real.sqrt 6 := by 
      have h13 : a^2 = (6 : ℝ) := h11
      have h15 : Real.sqrt (6 : ℝ) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by linarith)
      have h16 : a < 0 := ha 
      have h17 : a^2 = 6 := by nlinarith 
      have h18 : a = -Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg (6 : ℝ), h15]
      linarith 
    linarith 
  linarith