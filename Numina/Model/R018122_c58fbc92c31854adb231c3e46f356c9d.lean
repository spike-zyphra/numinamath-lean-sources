import Mathlib

theorem algebra_244082 {x y z : ℝ} (h1 : x + y + z = 15) (h2 : x^2 + y^2 + z^2 = 81)
    (h3 : x * y + x * z = 3 * y * z) :
    (x = 6 ∧ y = 3 ∧ z = 6) ∨ (x = 6 ∧ y = 6 ∧ z = 3) := by
  have h4 : z = 15 - x - y := by linarith
  rw [h4] at h2 h3
  have h5 : (x - 6) * (x - 9) = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (15 - x - y)), sq_nonneg (y - (15 - x - y))]
  have hx1 : x = 6 ∨ x = 9 := by 
    cases (mul_eq_zero.1 h5) with 
    | inl h => 
      left 
      linarith 
    | inr h => 
      right 
      linarith 
  cases hx1 with 
  | inl hx6 => 
    have hx6 : x = 6 := hx6 
    have eq_y : (y - 3) * (y - 6) = 0 := by 
      nlinarith 
    cases (mul_eq_zero.1 eq_y) with 
    | inl hy3 => 
      have hy3 : y = 3 := by linarith 
      have hz6 : z = 6 := by 
        rw [hx6, hy3] at h4 
        linarith 
      left 
      exact ⟨by linarith, by linarith, by linarith⟩ 
    | inr hy6 => 
      have hy6 : y = 6 := by linarith 
      have hz3 : z = 3 := by 
        rw [hx6, hy6] at h4 
        linarith 
      right 
      exact ⟨by linarith, by linarith, by linarith⟩ 
  | inr hx9 => 
    nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 3), sq_nonneg (z - 6), sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (z - 3)]