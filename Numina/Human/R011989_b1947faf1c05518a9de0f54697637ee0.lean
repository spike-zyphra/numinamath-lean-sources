import Mathlib

open Real Nat
open scoped BigOperators

theorem algebra_324732 :
  ∃ n : ℕ, ∀ m : ℕ, n < m → (100^(m + 1) / (Nat.factorial (m + 1) : ℝ)) < (100^m / (Nat.factorial m : ℝ)) := by 
  use 100
  intro m hm
  have ineq : (100 ^ (m + 1) / ((m + 1).factorial : ℝ)) / (100 ^ m / m.factorial : ℝ) < 1 := by 
    field_simp
    have aux : 100 ^ (m + 1) * ↑m.factorial / (↑(m + 1).factorial * 100 ^ m)
      = 100 / (m + 1 : ℝ) := by 
      field_simp
      have aux1 : (m + 1).factorial = m.factorial * (m + 1) := by 
        conv => 
          lhs
          unfold factorial
        simp
        ring
      rw [aux1]
      have aux2 : (100 : ℝ) ^ (m + 1) = (100 : ℝ) ^ m * 100 := by 
        exact rfl
      rw [aux2]
      norm_cast
      ring
    rw [aux]
    refine Bound.div_lt_one_of_pos_of_lt ?_ ?_
    linarith
    norm_cast
    linarith
  have pos : (100 ^ m / (m.factorial : ℝ)) > 0 := by 
    have pos1 : 100 ^ m > 0 := by positivity
    have pos2 : m.factorial > 0 := Nat.factorial_pos m
    positivity
  obtain h1 := (div_lt_iff₀ pos).mp ineq 
  linarith