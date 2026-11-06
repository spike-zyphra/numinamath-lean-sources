import Mathlib

/-
The reverse of a two-digit integer is the number obtained by reversing the order of its digits. For example, 34 is the reverse of 43. How many numbers exist such that when added to their reverse, they give a perfect square?
-/

theorem number_theory_243844:
{n : ℕ | 10 ≤ n ∧ n ≤ 99 ∧ IsSquare (n + (Nat.ofDigits 10 ((Nat.digits 10 n).reverse)))}.ncard = 8 := by 

  --We show that the following 8 numbers are exactly what we need.
  have cla : {n : ℕ | 10 ≤ n ∧ n ≤ 99 ∧ IsSquare (n + (Nat.ofDigits 10 ((Nat.digits 10 n).reverse)))} = {29,38,47,56,65,74,83,92} := by 
    ext n; simp
    constructor <;> intro h

    --From left to right, simple enumeration.
    obtain ⟨nl,nu,h⟩ := h
    interval_cases n <;> 
    simp [Nat.ofDigits_eq_foldr] at h ⊢ <;>
    absurd h <;>
    native_decide

    -- From right to left, we check that every number is valid.
    rcases h with h |  h |  h |  h |  h |  h |  h |  h <;>
    simp [h, Nat.ofDigits_eq_foldr] <;>
    native_decide

  --Then, we verify that this set has size 8.
  simp [cla]
  rw [Set.ncard_eq_succ]
  use 29
  use {38, 47, 56, 65, 74, 83, 92}
  simp
  rw [Set.ncard_eq_succ]
  use 38
  use {47,56,65,74,83,92}
  simp
  rw [Set.ncard_eq_succ]
  use 47
  use {56,65,74,83,92}
  simp
  rw [Set.ncard_eq_succ]
  use 56
  use {65,74,83,92}
  simp
  rw [Set.ncard_eq_succ]
  use 65
  use {74,83,92}
  simp


  