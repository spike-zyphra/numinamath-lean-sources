import Mathlib

open Finset

theorem number_theory_290844 (n : ℕ) (hn : n = ∏ i ∈ Icc 1 20, i) :
    ¬∃ m : ℕ, m > 0 ∧ n / 10 * m ∈ Icc 1 9 ∧ ¬∃ p : ℕ, p > 0 ∧ n / 10 * p ∈ Icc 1 9 := by
  intro h
  rcases h with ⟨m, hm1, hm2, hm3⟩
  have h1 : ∃ p : ℕ, p > 0 ∧ n / 10 * p ∈ Icc 1 9 := by
    refine' ⟨m, hm1, hm2⟩
  have h2 : ¬∃ p : ℕ, p > 0 ∧ n / 10 * p ∈ Icc 1 9 := hm3
  exact h2 h1