import Mathlib

open Finset

theorem algebra_100487 {f : ℤ → ℤ} (hf : ∀ x, f x = 3 * x + 2) :
    ∃ m, 0 < m ∧ 1997 ∣ f^[99] m := by 
  use 3 ^ 1897 - 1
  constructor
  · -- Show m > 0
    have h2 : 3 ^ 1897 - 1 > 0 := by
      omega
    linarith
  · -- Show 1997 divides f^[99] m
    have h3 : ∀ k, f^[k] (3 ^ 1897 - 1) = 3 ^ k * (3 ^ 1897 - 1 + 1) - 1 := by
      intro k
      induction k with
      | zero =>
        simp [Function.iterate_zero_apply]
        <;> ring_nf
      | succ k ih =>
        simp [Function.iterate_succ_apply', hf] at ih ⊢
        rw [ih]
        <;> ring_nf
    have h4 : f^[99] (3 ^ 1897 - 1) = 3 ^ 1996 - 1 := by
      rw [h3 99]
      ring_nf
    rw [h4]
    native_decide