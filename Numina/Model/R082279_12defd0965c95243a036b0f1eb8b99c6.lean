import Mathlib

theorem algebra_103702 (k : ℝ) (x₁ x₂ : ℝ)
    (h₁ : x₁^2 - (k - 2) * x₁ + (k^2 + 3 * k + 5) = 0)
    (h₂ : x₂^2 - (k - 2) * x₂ + (k^2 + 3 * k + 5) = 0)
    (h₃ : x₁ ≠ x₂) :
    x₁^2 + x₂^2 ≤ 18 := by
  have eq1 : (x₁ - x₂) * (x₁ + x₂ - (k - 2)) = 0 := by
    nlinarith [h₁, h₂]

  have h4 : (x₁ - x₂) = 0 ∨ (x₁ + x₂ - (k - 2)) = 0 := by 
    cases (mul_eq_zero.mp eq1) with 
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  
  cases h4 with 
  | inl h5 => 
    exfalso 
    apply h₃
    linarith
  | inr h6 => 
    have h₇ : x₁ + x₂ = k - 2 := by linarith
    have h₈ : x₁ * x₂ = k^2 + 3 * k + 5 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₃), h₇]
    have h₉ : (k - 2)^2 - 4 * (k^2 + 3 * k + 5) > 0 := by 
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₃), h₇, h₈]
    have h10 : x₁^2 + x₂^2 = (x₁ + x₂)^2 - 2 * (x₁ * x₂) := by 
      nlinarith
    rw [h10]
    rw [h₇, h₈]
    nlinarith [sq_nonneg (k + 4), sq_nonneg (k + 4/3), sq_nonneg (k - (-4/3)), sq_nonneg (k - (-4)), h₉]