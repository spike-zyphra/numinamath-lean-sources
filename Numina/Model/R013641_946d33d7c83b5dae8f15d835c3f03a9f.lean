import Mathlib

open Finset

theorem number_theory_301491 {g : ℕ → ℕ} (hg : ∀ k, Odd (g k) ∧ g k ∣ k ∧ ∀ d, Odd d → d ∣ k → d ≤ g k)
    (n : ℕ) :
    ∑ i ∈ range (2 ^ n), g (i + 1) = (4 ^ n + 2) / 3 := by
  have h1 : Odd (g 0) := (hg 0).1
  have h2 : (g 0) ∣ 0 := (hg 0).2.1
  have h3 : Odd (g 0) := (hg 0).1
  have h71 : (g 0 + 2) ≤ g 0 := by 
    have h8 : Odd (g 0 + 2) := by 
      have h9 : Odd (g 0) := h1
      rcases h9 with ⟨k, hk⟩ 
      use k + 1 
      omega 
    have h10 : (g 0 + 2) ∣ (0 : ℕ) := by 
      use 0 
      all_goals linarith 
    have h11 : (g 0 + 2) ≤ g 0 := by 
      apply (hg 0).2.2 
      · exact h8 
      · exact h10 
    linarith 
  linarith