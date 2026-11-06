import Mathlib

open Finset

theorem algebra_51248 {a b : ℕ → ℚ}
    (ha : ∀ k, a k = (k ^ 2 + 1) * k.factorial)
    (hb : ∀ k, b k = ∑ i in Icc 1 k, a i) :
    ∃ m n : ℕ, m.Coprime n ∧ a 100 / b 100 = m / n := by
  use 10001, 10100
  norm_num [ha, hb, sum_range_succ]
  <;> native_decide