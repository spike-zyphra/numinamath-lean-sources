import Mathlib

open Finset

theorem algebra_164641 {f : ℕ → ℕ} (hf : ∀ x, f x = x ^ 2 - 2) :
    (f^[24] 18) % 89 = 47 := by 
  have h1 : ∀ x, f x = x ^ 2 - 2 := hf
  simp [Function.iterate_succ_apply', h1]