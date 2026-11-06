import Mathlib

theorem number_theory_984 (x y : ℤ) (h₀ : 0 ≤ x ∧ x ≤ 9) (h₁ : 0 ≤ y ∧ y ≤ 9)
    (h₂ : 3 ∣ (50000 + 3000 + 800 + 10 * x + y)) (h₃ : 7 ∣ (50000 + 3000 + 800 + 10 * x + y))
    (h₄ : 11 ∣ (50000 + 3000 + 800 + 10 * x + y)) :
    x ^ 2 - y ^ 2 = -5 := by 
  have h5 : x ≤ 9 := h₀.right
  have h6 : 0 ≤ x := h₀.left
  have h7 : y ≤ 9 := h₁.right
  have h8 : 0 ≤ y := h₁.left
  have h9 : x ≤ 9 := by linarith
  have h10 : y ≤ 9 := by linarith
  interval_cases x <;> interval_cases y <;> omega 
  <;> norm_num at h₂ h₃ h₄ <;> omega