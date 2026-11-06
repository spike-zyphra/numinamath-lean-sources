import Mathlib

theorem algebra_187419 (a : ℕ → ℝ) (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * a n / n) :
    a 100 = 10100 := by
  norm_num [ha1, han]
  <;> try ring_nf <;> norm_num
  <;> try ring_nf <;> norm_num