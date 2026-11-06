import Mathlib

  theorem number_theory_285499 (N : ℕ) (hN : N > 200 ∧ N < 300) (h : 2007 % N = 5) :
    N = 286 := by
  rcases hN with ⟨h1, h2⟩
  interval_cases N <;> norm_num at h ⊢ <;> all_goals omega