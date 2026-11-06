import Mathlib

theorem algebra_60021 {x y z : ℝ} (h1 : x + y - z = 4) (h2 : x^2 - y^2 + z^2 = -4) (h3 : x * y * z = 6) :
    (x, y, z) = (2, 3, 1) ∨ (x, y, z) = (-1, 3, -2) := by
  have h4 : z = x + y - 4 := by linarith
  rw [h4] at h2
  have eq1 : x ^ 2 + x * y - 4 * (x + y) + 10 = 0 := by
    nlinarith 
  rw [h4] at h3
  have eq2 : x * y * (x + y - 4) = 6 := by 
    linarith
  have h5 : y^2 = 9 := by 
    nlinarith [ sq_nonneg (y^2), sq_nonneg (x + 2), sq_nonneg ( (x + y) - 3 ), sq_nonneg ( (x + y) + 2 ), sq_nonneg (x - 4), sq_nonneg (y - 3), sq_nonneg (y + 3) ]
  have h6 : y = 3 ∨ y = -3 := by
    have h7 : y ^ 2 = 9 := h5 
    have : y = 3 ∨ y = -3 := by
      have h8 : y ^ 2 - 9 = 0 := by linarith
      have h9 : (y - 3) * (y + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- case y-3 = 0
        left
        linarith
      · -- case y+3 = 0
        right
        linarith
    simpa using this
  cases h6 with
  | inl hy3 => -- Let's suppose that $y=3$.
    have eq3 : x = 2 ∨ x = -1 := by 
      have eq4 : x^2 - x - 2 = 0 := by 
        rw [show y = 3 by linarith [hy3]] at eq1 
        nlinarith 
      have : (x - 2) * (x + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 this) with h8 h9 
      · left 
        linarith 
      · right 
        linarith 
    cases eq3 with 
    | inl eq3 => -- x = 2 
      have eq4 : z = 1 := by
        rw [eq3, show y = 3 by linarith [hy3]] at h4 
        nlinarith 
      left 
      simp [eq3, hy3, eq4]
    | inr eq3 => -- x = -1 
      have eq4 : z = -2 := by
        rw [eq3, show y = 3 by linarith [hy3]] at h4 
        nlinarith 
      right 
      simp [eq3, hy3, eq4]
  | inr hy_3 => -- Let's suppose that $y=-3$.
    have eq3 : x^2 + 3*x + 8 = 0 := by
      rw [show y = -3 by linarith [hy_3]] at eq1 
      nlinarith 
    exfalso 
    have : (x^2 + 3*x + 8) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    nlinarith [ sq_nonneg (x + 3 / 2 ) ]