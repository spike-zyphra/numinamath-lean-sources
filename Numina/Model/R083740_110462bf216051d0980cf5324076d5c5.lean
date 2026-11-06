import Mathlib

open Finset

theorem algebra_183746 {a : ℝ} (ha : 0 < a ∧ a < 1) (x : ℕ → ℝ)
    (hx1 : x 1 = a) (hxn : ∀ n, x (n + 1) = a ^ x n) :
    Odd n → x n < x (n + 2) ∧ Even n → x (n + 2) < x n := by
  intro h_odd_n h
  have h1 : Odd n := h_odd_n 
  have h2 : Even n := h.2
  have h3 : ¬ Odd n := by 
    simp [Nat.not_odd_iff_even, h2]
  contradiction