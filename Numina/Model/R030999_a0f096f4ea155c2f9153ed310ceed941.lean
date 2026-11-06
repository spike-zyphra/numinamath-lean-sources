import Mathlib

open Finset

theorem algebra_286987 {a : ℕ → ℤ} (ha : ∀ k, a k = ∑ i ∈ Icc 1 99, (Nat.choose i k)) :
    ⌊(a 4 : ℝ) / a 3⌋ = 19 := by
  have h3 : a 3 = ∑ i ∈ Icc 1 99, (Nat.choose i 3) := ha 3
  have h4 : a 4 = ∑ i ∈ Icc 1 99, (Nat.choose i 4) := ha 4

  have eq1 : a 3 = (Nat.choose 100 4 : ℤ) := by
    rw [h3]
    native_decide
  have eq2 : a 4 = (Nat.choose 100 5 : ℤ) := by
    rw [h4]
    native_decide

  have eq3' : (a 4 : ℝ) = (Nat.choose 100 5 : ℝ) := by
    exact_mod_cast eq2

  have eq4' : (a 3 : ℝ) = (Nat.choose 100 4 : ℝ) := by
    exact_mod_cast eq1

  have h5 : (a 4 : ℝ) / (a 3 : ℝ) = (96 / 5 : ℝ) := by
    rw [eq3', eq4']
    norm_num [Nat.choose]

  have h6 : ⌊(a 4 : ℝ) / a 3⌋ = 19 := by
    rw [h5]
    norm_num [Int.floor_eq_iff]

  exact h6