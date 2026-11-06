import Mathlib

theorem algebra_223005 (x y z : ℝ) (h₀ : x + y + x * y = 19) (h₁ : y + z + y * z = 11) (h₂ : z + x + z * x = 14) :
    (x, y, z) = (4, 3, 2) ∨ (x, y, z) = (-6, -5, -4) := by
  have h3 : (x + 1) * (y + 1) = 20 := by 
    nlinarith 
  have h4 : (y + 1) * (z + 1) = 12 := by 
    nlinarith 
  have h5 : (z + 1) * (x + 1) = 15 := by
    nlinarith 
  have h6 : (x + 1) ^ 2 = 25 := by
    nlinarith [sq_nonneg ((x + 1) * (y + 1) * (z + 1)), sq_nonneg (y + 1), sq_nonneg (z + 1), sq_nonneg (x + 1)]
  have h7 : (x + 1) = 5 ∨ (x + 1) = -5 := by
    have h8 : (x + 1) ^ 2 - 25 = 0 := by nlinarith
    have h9 : (x + 1) ^ 2 - 25 = ( (x + 1) - 5 ) * ( (x + 1) + 5 ) := by ring 
    rw [h9] at h8
    cases (mul_eq_zero.1 h8) with
    | inl h10 =>
      left
      linarith
    | inr h11 =>
      right
      linarith
  cases h7 with
  | inl h7 =>
    have hx1 : x = 4 := by linarith
    have hy1 : y = 3 := by
      have h8 : (x + 1) * (y + 1) = 20 := by nlinarith 
      rw [show x + 1 = 5 by linarith [h7]] at h8
      nlinarith
    have hz1 : z = 2 := by
      have h8 : (y + 1) * (z + 1) = 12 := by nlinarith 
      rw [show y + 1 = 4 by nlinarith [hy1]] at h8
      nlinarith
    left
    simp [hx1, hy1, hz1]
    all_goals tauto
  | inr h7 =>
    have hx2 : x = -6 := by linarith
    have hy2 : y = -5 := by
      have h8 : (x + 1) * (y + 1) = 20 := by nlinarith 
      rw [show x + 1 = -5 by linarith [h7]] at h8
      nlinarith
    have hz2 : z = -4 := by
      have h8 : (y + 1) * (z + 1) = 12 := by nlinarith 
      rw [show y + 1 = -4 by nlinarith [hy2]] at h8
      nlinarith
    right
    simp [hx2, hy2, hz2]
    all_goals tauto