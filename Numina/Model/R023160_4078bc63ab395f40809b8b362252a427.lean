import Mathlib

open Real

theorem number_theory_219998 (Prohibited : Set ℕ) (hProhibited : Finite Prohibited)
    (hExist : ∃ x, ∀ n, ¬(∃ k, k ∈ Prohibited ∧ (Nat.floor (10 ^ n * x)) % 10 ^ k = 0)) :
    ∃ y, ∀ n, ¬(∃ k, k ∈ Prohibited ∧ (Nat.floor (10 ^ n * y)) % 10 ^ k = 0) ∧
    ∃ p, Function.Periodic (fun n => (Nat.floor (10 ^ n * y)) % 10 ^ p) p := by 
  rcases hExist with ⟨x, hx⟩
  use x
  intro n
  constructor
  · exact hx n
  · use 0
    simp [Function.Periodic]
    all_goals try { tauto }