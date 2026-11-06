import Mathlib

theorem inequalities_2229 (a b c x y z M N P Q : ℝ)
    (h₀ : a > b ∧ b > c) (h₁ : x > y ∧ y > z)
    (h₂ : M = a * x + b * y + c * z)
    (h₃ : N = a * z + b * y + c * x)
    (h₄ : P = a * y + b * z + c * x)
    (h₅ : Q = a * z + b * x + c * y) :
    M > P ∧ P > N ∧ M > Q ∧ Q > N := by
  have h5 : M > P := by 
    rw [h₂, h₄]
    nlinarith [h₀.1, h₀.2, h₁.1, h₁.2, mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.2), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.2)]
  have h7 : P > N := by 
    rw [h₄, h₃]
    nlinarith [h₀.1, h₀.2, h₁.1, h₁.2, mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.2), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.2)]
  have h8 : M > Q := by 
    rw [h₂, h₅]
    nlinarith [h₀.1, h₀.2, h₁.1, h₁.2, mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.2), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.2)]
  have h9 : Q > N := by 
    rw [h₅, h₃]
    nlinarith [h₀.1, h₀.2, h₁.1, h₁.2, mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.1) (sub_pos.mpr h₁.2), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.1), mul_pos (sub_pos.mpr h₀.2) (sub_pos.mpr h₁.2)]
  constructor
  · exact h5
  constructor
  · exact h7
  constructor
  · exact h8
  · exact h9