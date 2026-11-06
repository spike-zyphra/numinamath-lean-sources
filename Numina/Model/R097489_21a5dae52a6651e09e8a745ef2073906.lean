import Mathlib

open Finset Real

theorem algebra_126465 {a : ℝ} (ha : 0 < a ∧ a < 1) (x : ℕ → ℝ)
    (hx1 : x 1 = a) (hxn : ∀ n, x (n + 1) = a ^ x n) :
    ∀ n, Odd n → x n < x (n + 2) ∧ Even n → x (n + 2) < x n := by 
  intro n hn1 hn2
  have h2 : Even n := hn2.right
  have h1 : Odd n := hn1
  have h3 : ¬ Odd n := by
    exact Nat.not_odd_iff_even.mpr h2
  contradiction