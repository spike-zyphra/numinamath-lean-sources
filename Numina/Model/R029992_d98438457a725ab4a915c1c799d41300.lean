import Mathlib

theorem number_theory_4083 (a : ℕ → ℕ) (ha₀ : a 0 = 155) (ha₁ : ∀ n, a (n + 1) = a n - 4) :
    a 8 = 123 := by 
  have ha1 : a 1 = a 0 - 4 := ha₁ 0
  have ha2 : a 2 = a 1 - 4 := ha₁ 1
  have ha3 : a 3 = a 2 - 4 := ha₁ 2
  have ha4 : a 4 = a 3 - 4 := ha₁ 3
  have ha5 : a 5 = a 4 - 4 := ha₁ 4
  have ha6 : a 6 = a 5 - 4 := ha₁ 5
  have ha7 : a 7 = a 6 - 4 := ha₁ 6
  have ha8 : a 8 = a 7 - 4 := ha₁ 7
  rw [ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1, ha₀]
  all_goals omega