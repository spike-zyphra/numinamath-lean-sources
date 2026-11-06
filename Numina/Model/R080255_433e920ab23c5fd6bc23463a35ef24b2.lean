import Mathlib

theorem algebra_288012 (x : ℕ) :
    3^x = 3^20 * 3^20 * 3^18 + 3^19 * 3^20 * 3^19 + 3^18 * 3^21 * 3^19 ↔ x = 59 := by 
  constructor
  · -- Assume the equation holds, derive x = 59
    intro h
    have eq1 : 3^x = 3^59 := by
      norm_num at h ⊢
      omega
    have h1 : x = 59 := by
      exact Nat.pow_right_injective (by norm_num) eq1
    exact h1
  · -- Assume x = 59, prove the equation
    intro h
    rw [h]
    norm_num