import Mathlib

theorem number_theory_240735 (A : ℕ) (hA : A.Prime ∧ A < 100)
    (hA1 : (A + 10).Prime) (hA2 : (A - 20).Prime) (hA3 : (A + 30).Prime)
    (hA4 : (A + 60).Prime) (hA5 : (A + 70).Prime) :
    A = 37 ∨ A = 43 ∨ A = 79 := by
  have h2 : A < 100 := hA.right
  have h1 : A.Prime := hA.left

  interval_cases A <;> norm_num at h1 hA1 hA2 hA3 hA4 hA5 ⊢ <;> try tauto