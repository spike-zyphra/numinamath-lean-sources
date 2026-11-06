import Mathlib

open Finset

theorem number_theory_72813 {n : ℕ} (hn : 2 ≤ n) (p : ℕ) (hp : Nat.Prime p) :
    ∃ k, (1 / (p - 1 : ℚ)) * ∑ a ∈ Icc 1 (p - 1), {x | ∃ c, (c ^ n + a * c) % p = x}.ncard = k := by 
  refine' ⟨(1 / (p - 1 : ℚ)) * ∑ a ∈ Icc 1 (p - 1), {x | ∃ c, (c ^ n + a * c) % p = x}.ncard, by simp⟩