import Mathlib

open Finset

theorem number_theory_35493 {f : ℕ → ℕ}
    (hf : ∀ x, Odd x → f x = 3 * x + 1)
    (hf' : ∀ x, Even x → f x = x / 2) :
    ∃ x, f^[40] x > 2012 * x := by
  use 2^100 - 1
  set x := 2^100 - 1 with hx1
  rw [hx1]
  simp [Function.iterate_succ_apply', Nat.odd_iff, Nat.even_iff, hf, hf']
  <;> native_decide