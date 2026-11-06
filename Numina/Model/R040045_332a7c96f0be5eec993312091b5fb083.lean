import Mathlib

theorem number_theory_198822 :
    ∃ k : ℕ, ∃ a : Fin k → ℕ,
      (∀ i, a i ≥ 1) ∧
      (∑ i, a i) = 1984 ∧
      (∑ i, (1 : ℚ)/(a i)) = 1 := by

  use 42

  use fun i => 
    if i.val < 22 then 62 else 31

  constructor
  · -- Show that all numbers are ≥ 1
    intro i
    fin_cases i <;> simp

  constructor
  · -- Show that the sum is 1984
    native_decide

  · -- Show that the reciprocal sum is 1
    native_decide