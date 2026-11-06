import Mathlib

def I : Set ℤ := {x | 1 ≤ x ∧ x ≤ 100}

def A : Set ℤ := {m | 1 ≤ m ∧ m ≤ 100 ∧ ∃ k, m = 2 * k + 1}

def B : Set ℤ := {n | 1 ≤ n ∧ n ≤ 100 ∧ ∃ k, n = 3 * k}

theorem number_theory_144063 :
    IsGreatest {x | x ∈ I ∧ ¬x ∈ A ∧ x ∈ B} 96 := by
  constructor
  · -- Show 96 is in the set.
    constructor
    · -- Show 96 ∈ I.
      show 96 ∈ I
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show ¬(96 ∈ A).
      show ¬ (96 ∈ A)
      intro h
      rcases show 96 ∈ A by simpa using h with ⟨h1, h2, ⟨k, hk⟩⟩
      omega
    · -- Show 96 ∈ B.
      show 96 ∈ B
      refine' ⟨by norm_num, by norm_num, ?_⟩
      use 32
      all_goals norm_num
  · -- Show 96 is greatest in the set.
    intro x hx
    rcases hx with ⟨h1, h2, h3⟩
    rcases show x ∈ I by simpa using h1 with ⟨h11, h12⟩
    rcases show x ∈ B by simpa using h3 with ⟨h13, h14, ⟨k, hk⟩⟩
    -- Show that x is even.
    have h41 : x % 2 = 0 := by
      by_contra h42
      push_neg at h42
      have h11 : x % 2 = 1 := by omega
      have h4 : x ∈ A := by
        refine ⟨by omega, by omega, ?_⟩
        refine ⟨(x - 1) / 2, by omega⟩
      tauto
    -- Now we know x is a multiple of 2 and a multiple of 3, so it's a multiple of 6.
    omega