import Mathlib

theorem algebra_3657 {x y : ℝ} (h₀ : x ≠ -y) (h₁ : x ≠ y)
  (h₂ : 6 / (x + y) + 1 / (x - y) = 3) (h₃ : 3 / (x + y) + 3 / (x - y) = 4) :
  x + 3 * y = 5 := by

  have h4 : x + y ≠ 0 := by
    intro h5
    have h6 : x = -y := by linarith
    contradiction

  have h5 : x - y ≠ 0 := by
    intro h6
    have h7 : x = y := by linarith
    contradiction

  have eq1 : 6 * (x - y) + (x + y) = 3 * (x + y) * (x - y) := by
    have h6 : (x + y) * (x - y) ≠ 0 := by
      apply mul_ne_zero 
      · exact h4
      · exact h5

    field_simp [h6] at h₂ ⊢ 
    linarith

  have eq2 : 3 * (x - y) + 3 * (x + y) = 4 * (x + y) * (x - y) := by
    have h6 : (x + y) * (x - y) ≠ 0 := by
      apply mul_ne_zero 
      · exact h4
      · exact h5

    field_simp [h6] at h₃ ⊢ 
    linarith

  have eq3 : 7 * x - 5 * y = 3 * ((x + y) * (x - y)) := by
    linarith [eq1]

  have eq4 : 6 * x = 4 * ((x + y) * (x - y)) := by
    linarith [eq2]

  have eq5 : (x + y) * (x - y) = 3 * x / 2 := by
    nlinarith

  have eq6 : 7 * x - 5 * y = 9 * x / 2 := by 
    rw [eq5] at eq3
    linarith

  have h8 : x = 2 * y := by
    linarith
  
  rw [show x = 2 * y by linarith [h8]] at eq4

  have eq7 : 12 * y = 12 * y ^ 2 := by
    nlinarith

  have h9 : y = 0 ∨ y = 1 := by
    have : 12 * y * (y - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp this) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  cases h9 with
  | inl h0 =>
    have h10 : x = 0 := by
      linarith [h8, h0]
    have h11 : x = y := by
      linarith [h10, h0]
    contradiction
  | inr h1 =>
    have h2 : x = 2 := by
      linarith [h8, h1]
    linarith [h2, h1]