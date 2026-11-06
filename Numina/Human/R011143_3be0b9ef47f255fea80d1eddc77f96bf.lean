import Mathlib

/-
What is the smallest number divisible by integers 1 through 9?
-/

theorem number_theory_15183 :
  IsLeast { n:ℕ | 0<n ∧ (∀ i∈(Finset.Icc 1 9), (i ∣ n))} 2520 := by
    unfold IsLeast
    constructor
    --2520 satisfies the assumptions.
    simp
    native_decide

    --For every such number a, we have 5 ∣ a, 7 ∣ a, 8 ∣ a, and 9 ∣ a.
    --Note that these four numbers are coprime, so the product  2520 also divides a.
    unfold lowerBounds
    simp

    intro a apos h
    have d9: 9 ∣ a := by specialize h 9; simp at h; exact h
    have d8: 8 ∣ a := by specialize h 8; simp at h; exact h
    have d7: 7 ∣ a := by specialize h 7; simp at h; exact h
    have d5: 5 ∣ a := by specialize h 5; simp at h; exact h

    have : Nat.Coprime 9 8 := by norm_num
    have d98: 9 * 8 ∣ a := by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd this d9 d8
    have : Nat.Coprime 7 5 := by norm_num
    have d75: 7 * 5 ∣ a := by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd this d7 d5
    simp at d98 d75
    have : Nat.Coprime 72 35 := by norm_num
    have dd: 72 * 35 ∣ a := by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd this d98 d75
    simp at dd
    
    have ag : 2520 ≤ a := by apply Nat.le_of_dvd at dd; exact dd; exact apos
    exact ag
