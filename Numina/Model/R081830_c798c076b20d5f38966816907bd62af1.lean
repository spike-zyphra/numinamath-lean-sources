import Mathlib

theorem algebra_57996 : IsGreatest {x : ℤ | ∃ A M C : ℕ, A + M + C = 10 ∧ x = A * M * C + A * M + M * C + C * A} 69 := by
  constructor
  · -- Show that 69 is in the set
    use 3, 3, 4
    all_goals norm_num
  · -- Show that 69 is the greatest
    intro x hx
    rcases hx with ⟨A, M, C, hsum, hx⟩
    have h1 : (A : ℤ) + (M : ℤ) + (C : ℤ) = 10 := by
      norm_num at hsum ⊢
      exact_mod_cast hsum
    have h2 : (x : ℤ) = (A : ℤ) * (M : ℤ) * (C : ℤ) + (A : ℤ) * (M : ℤ) + (M : ℤ) * (C : ℤ) + (C : ℤ) * (A : ℤ) := by
      norm_num at hx ⊢
      exact_mod_cast hx
    have h3 : A ≤ 10 := by
      omega
    have h4 : M ≤ 10 := by
      omega
    have h5 : C ≤ 10 := by
      omega
    -- Lean will check all possible integer combinations to verify that the maximum is 69
    interval_cases A <;> interval_cases M <;> omega