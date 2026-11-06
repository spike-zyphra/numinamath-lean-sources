import Mathlib

open Finset

theorem number_theory_109608 (T : Set ℕ) (hT : T = {x | ∃ α β γ : ℕ, x = 2^α * 5^β * 7^γ ∧ (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0)}) :
    ∀ n : ℕ, ∃ m : ℕ, m > n ∧ ∃ s : Finset ℕ, m = ∑ i ∈ s, i ∧ ∀ i ∈ s, i ∈ T ∧ ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(i ∣ j) := by
  intro n
  use 5 ^ (n + 1)
  constructor
  · -- Show that 5^(n+1) > n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      simp [Nat.pow_succ, Nat.mul_add] at ih ⊢
      omega
  · -- Show the existence of a finite set
    use {5 ^ (n + 1)}
    constructor
    · -- Show that the sum equals m 
      simp
    · -- Show that all elements are in T and no divisibility relationships 
      intro i hi
      have h2 : i = 5 ^ (n + 1) := by 
        have h2 : i ∈ ({5 ^ (n + 1)} : Finset ℕ) := hi 
        simp at h2 ⊢ 
        all_goals tauto 
      have h3 : i ∈ T := by 
        rw [hT]
        rw [h2]
        use 0, n + 1, 0 
        constructor 
        · -- Show the equality 
          simp 
        · -- Show the condition 
          simp 
      have h4 : ∀ i ∈ ({5 ^ (n + 1)} : Finset ℕ), ∀ j ∈ ({5 ^ (n + 1)} : Finset ℕ), i ≠ j → ¬(i ∣ j) := by 
        intro i hi j hj hne
        have h2 : i = 5 ^ (n + 1) := by 
          have h2 : i ∈ ({5 ^ (n + 1)} : Finset ℕ) := hi 
          simp at h2 ⊢ 
          all_goals tauto 
        have h3 : j = 5 ^ (n + 1) := by 
          have h3 : j ∈ ({5 ^ (n + 1)} : Finset ℕ) := hj 
          simp at h3 ⊢ 
          all_goals tauto 
        have h4 : i = j := by 
          omega 
        omega 
      tauto