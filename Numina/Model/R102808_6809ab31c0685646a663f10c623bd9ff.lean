import Mathlib

theorem algebra_177709 {A B C : ℝ} (h : ∀ x, x ≠ 1 ∧ x ≠ -2 → (x^2 + 5) / (x^3 - 3 * x + 2) = A / (x + 2) + B / (x - 1)^2 + C / (x - 1)) :
    A = 1 ∧ B = 2 ∧ C = 0 := by 

  have eqn1 := h 0 ⟨by norm_num, by norm_num⟩
  have eqn2 := h 2 ⟨by norm_num, by norm_num⟩
  have eqn3 := h (-1 : ℝ) ⟨by norm_num, by norm_num⟩
  have eqn4 := h 3 ⟨by norm_num, by norm_num⟩
  
  norm_num at eqn1 eqn2 eqn3 eqn4
  
  constructor
  · -- Prove A = 1
    linarith
  
  constructor
  · -- Prove B = 2
    linarith
  
  · -- Prove C = 0
    linarith