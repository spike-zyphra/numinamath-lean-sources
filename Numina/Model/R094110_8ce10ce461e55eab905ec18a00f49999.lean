import Mathlib

theorem algebra_130257 {x y : ℝ} (h₀ : x^2 + y^2 = 25) (h₁ : x + y + x * y = 19) :
    (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) := by
  have h2 : (x + y) ^ 2 - 2 * (x * y) = 25 := by
    nlinarith
  have h3 : (x + y) + (x * y) = 19 := by 
    linarith
  have h4 : (x + y) ^ 2 + 2 * (x + y) - 63 = 0 := by
    nlinarith [h2, h3]
  have h5 : (x + y - 7) * (x + y + 9) = 0 := by 
    ring_nf at h4 ⊢
    nlinarith 
  cases (mul_eq_zero.mp h5) with
  | inl h6 =>
    have h7 : x + y = 7 := by linarith
    have h8 : x * y = 12 := by 
      nlinarith [h3, h7]
    have h9 : (x - 3) * (x - 4) = 0 := by
      nlinarith 
    cases (mul_eq_zero.mp h9) with
    | inl h10 =>
      have hx : x = 3 := by linarith 
      have hy : y = 4 := by linarith [h7, hx] 
      left 
      exact ⟨hx, hy⟩ 
    | inr h11 =>
      have hx : x = 4 := by linarith 
      have hy : y = 3 := by linarith [h7, hx] 
      right 
      exact ⟨hx, hy⟩ 
  | inr h6 =>
    have h7 : x + y = -9 := by linarith 
    have h8 : x * y = 28 := by 
      nlinarith [h3, h7]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]