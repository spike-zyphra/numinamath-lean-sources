import Mathlib

open Finset

theorem number_theory_122492 {b : ℕ} (hb : 2 ≤ b) :
    ∀ n, ∃! d : List ℕ, Nat.digits b n = d := by
  intro n
  use Nat.digits b n
  simp