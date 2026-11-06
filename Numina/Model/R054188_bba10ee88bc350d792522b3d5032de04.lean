import Mathlib

theorem number_theory_200848 (s : Finset ℕ) (h₀ : s = {27720, 55440, 83160, 110880, 138600, 166320}) :
    s.card = 6 ∧ ∀ m ∈ s, ∀ n ∈ s, m ≠ n → (m * n) % (m + n) = 0 := by 
  constructor
  · -- Show that s has exactly 6 elements
    rw [h₀]
    native_decide
  · -- Show the divisibility condition for all distinct pairs
    intro m hm n hn hmn
    rw [h₀] at hm hn
    fin_cases hm <;> fin_cases hn <;> norm_num at *
    <;> omega