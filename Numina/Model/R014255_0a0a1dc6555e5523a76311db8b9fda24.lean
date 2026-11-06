import Mathlib

theorem algebra_228471 {x y : ℝ} (h₀ : x^3 - y^3 = 26) (h₁ : x^2 * y - x * y^2 = 6) :
    (x = 3 ∧ y = 1) ∨ (x = -1 ∧ y = -3) := by 
  have eq1 : (x - y) ^ 3 + 3 * (x^2 * y - x * y^2) = x^3 - y^3 := by
    ring
  have h2 : (x - y) ^ 3 + 3 * (x^2 * y - x * y^2) = 26 := by
    linarith [h₀, eq1]
  have h3 : (x - y) ^ 3 + 18 = 26 := by
    have h4 : x^2 * y - x * y^2 = 6 := h₁
    nlinarith [h2, h4]
  -- Subtract 26 from both sides to get the equation to solve
  have h4 : (x - y) ^ 3 = 8 := by 
    linarith [h3]
  -- Solving the previous equation
  have h5 : x - y = 2 := by 
    have h6 : (x - y) ^ 3 - 8 = 0 := by linarith [h4]
    have h7 : (x - y) ^ 3 - 8 = (x - y - 2) * ((x - y) ^ 2 + 2 * (x - y) + 4) := by ring
    rw [h7] at h6
    cases' (mul_eq_zero.1 h6) with h8 h9
    · -- First case where x - y - 2 = 0, so x - y = 2
      linarith
    · -- Second case where (x - y) ^ 2 + 2 * (x - y) + 4 = 0 
      nlinarith [sq_nonneg ((x - y) + 1)]
  have h5' : x - y = 2 := h5
  have h7 : x * y = 3 := by
    have h8 : x^2 * y - x * y^2 = 6 := h₁
    have h9 : x^2 * y - x * y^2 = (x * y) * (x - y) := by ring
    rw [h9] at h8
    rw [show x - y = 2 by linarith] at h8
    linarith
  have h8 : x = y + 2 := by
    nlinarith
  rw [show x = y + 2 by linarith] at h7
  -- Now we can solve the quadratic equation 
  -- y^2 + 2y - 3 = 0
  -- Expanding:
  -- y^2 + 2 * y - 3 = 0
  -- (y + 3)(y - 1) = 0
  -- y = -3 or y = 1
  have h9 : y ^ 2 + 2 * y - 3 = 0 := by
    nlinarith
  have h10 : (y - 1) * (y + 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h10) with hy1 hy2
  · -- y - 1 = 0, so y = 1
    have hy1' : y = 1 := by linarith
    have hx1' : x = 3 := by 
      linarith [h8, hy1']
    left 
    exact ⟨hx1', hy1'⟩
  · -- y + 3 = 0, so y = -3 
    have hy2' : y = -3 := by linarith
    have hx2' : x = -1 := by 
      linarith [h8, hy2']
    right 
    exact ⟨hx2', hy2'⟩