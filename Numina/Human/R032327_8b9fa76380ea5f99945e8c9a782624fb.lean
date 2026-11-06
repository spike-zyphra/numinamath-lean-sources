import Mathlib

open Finset

/- Example 2 What is the maximum number of positive integers such that the sum of any three of them is a prime number? Prove your conclusion.
(2013, Peking University and other universities' independent enrollment examination) -/
theorem number_theory_328431 :
    IsGreatest { #S | (S : Finset ℕ) (_ : ∀ m ∈ S, m > 0) (_ : ∀ T ⊆ S, #T = 3 → (T.sum id).Prime) } 4 := by
  constructor
  -- We first verify that 4 is achievable.
  {
    -- {1, 3, 7, 9} satisfies the conditions
    use {1, 3, 7, 9}
    -- Which can be verified by calculation.
    native_decide
  }
  -- We now show that no larger set is possible.
  rintro n ⟨S, hS₀, hS, rfl⟩
  by_contra! hcard
  -- We partition the set into three residue classes modulo 3.
  have hsum := card_eq_sum_card_fiberwise (f := fun x => x % 3) (s := S) (t := range 3) (by simp [Nat.mod_lt])
  -- One of the following must be true:
  -- 1. Each residue class has at least one element.
  -- 2. One of the residue classes has at least 3 elements.
  -- If 1 does not hold, then there are at least 5 elements in two classes, so 2 must hold.
  obtain h | h : (∀ i ∈ range 3, 0 < #({x ∈ S | x % 3 = i})) ∨ (∃ i ∈ range 3, 3 ≤ #({x ∈ S | x % 3 = i})) := by
    -- We write the conditions in forms of {x ∈ S | x % 3 = 0}, {x ∈ S | x % 3 = 1}, {x ∈ S | x % 3 = 2}.
    simp [Finset.sum] at hsum
    rw [show range 3 = {0, 1, 2} from rfl]
    simp [-card_pos]
    -- We solve the linear system of inequalities of natural numbers by omega.
    omega
  . -- If 1 holds, then each residue class has at least one element.
    simp at h
    -- We take one element from each residue class.
    obtain ⟨x₀, h₀⟩ := h 0 (by simp)
    obtain ⟨x₁, h₁⟩ := h 1 (by simp)
    obtain ⟨x₂, h₂⟩ := h 2 (by simp)
    simp at h₀ h₁ h₂
    rcases h₀ with ⟨hx₀, h₀⟩
    rcases h₁ with ⟨hx₁, h₁⟩
    rcases h₂ with ⟨hx₂, h₂⟩
    -- We let T be the set of these three elements.
    let T : Finset ℕ := ⟨{x₀, x₁, x₂}, by
      -- x₀, x₁, x₂ are distinct since they have different residues modulo 3.
      simp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      all_goals
        intro h
        simp [h, h₀, h₁, h₂] at h₀ h₁ h₂
    ⟩
    -- T is a subset of S.
    have hT₁ : T ⊆ S := by
      intro x hx
      simp [T] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    -- T has 3 elements.
    have hT₂ : #T = 3 := by
      simp [Finset.card, T]
    specialize hS T hT₁ hT₂
    -- We now derive a contradiction from the hypothesis that the sum of T is prime.
    simp [T, Finset.sum] at hS
    replace hx₀ : x₀ > 0 := hS₀ x₀ hx₀
    replace hx₁ : x₁ > 0 := hS₀ x₁ hx₁
    replace hx₂ : x₂ > 0 := hS₀ x₂ hx₂
    clear S hS₀ hcard hsum h T hT₁ hT₂
    -- The sum of T is a multiple of 3.
    have h₃ : 3 ∣ x₀ + (x₁ + x₂) := by omega
    -- So the sum of T must be 3.
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hS] at h₃
    -- But that is clearly impossible.
    omega
  . -- If 2 holds, then one of the residue classes [i] has at least 3 elements.
    rcases h with ⟨i, hi, hcard₂⟩
    simp at hi
    -- We take a subset of [i] with 3 elements as T.
    obtain ⟨T, hT₁, hT₂⟩ := Finset.exists_subset_card_eq hcard₂
    specialize hS T (hT₁.trans (filter_subset _ _)) hT₂
    -- We now derive a contradiction from the hypothesis that the sum of T is prime.
    -- We write T as {x₀, x₁, x₂}.
    obtain ⟨x₀, x₁, x₂, h₀₁, h₀₂, h₁₂, rfl⟩ := Finset.card_eq_three.mp hT₂
    simp [h₀₁, h₀₂, h₁₂] at hS
    simp [Finset.instHasSubset] at hT₁
    rcases hT₁ with ⟨⟨hx₀, h₀⟩, ⟨hx₁, h₁⟩, ⟨hx₂, h₂⟩⟩
    -- We now derive a contradiction from the hypothesis that the sum of T is prime.
    replace hx₀ : x₀ > 0 := hS₀ x₀ hx₀
    replace hx₁ : x₁ > 0 := hS₀ x₁ hx₁
    replace hx₂ : x₂ > 0 := hS₀ x₂ hx₂
    -- The sum of T is a multiple of 3.
    have h₃ : 3 ∣ x₀ + (x₁ + x₂) := by omega
    -- So the sum of T must be 3.
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hS] at h₃
    -- But that is clearly impossible.
    omega
