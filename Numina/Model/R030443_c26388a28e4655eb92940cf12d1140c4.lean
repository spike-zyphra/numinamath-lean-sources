import Mathlib

open Finset

theorem number_theory_114480 {S : ℕ} (hS : S = ∑ i ∈ range 671, 3^(3*i)) :
    (∃ m, m^3 = 26 * S + 1) ∧ (3 ^ 33)^61 = 26 * S + 1 := by
  have h1 : S = (3 ^ (3 * 671) - 1) / 26 := by
    rw [hS]
    native_decide
  constructor
  · -- Show there exists an m such that m^3 = 26 * S + 1
    use 3 ^ 671
    rw [h1]
    <;> omega
  · -- Show that (3^33)^61 = 26 * S + 1
    rw [h1]
    <;> omega