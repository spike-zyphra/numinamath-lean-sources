import Mathlib

theorem algebra_14655 (a : ℕ → ℝ) (ha : a 0 = 28) (h : ∀ n, a (n + 1) = a n - 7) :
    ∑ i in Finset.range (Nat.ceil (a 0 / 7)), a i = 70 := by
  have h1 : a 0 = 28 := ha
  have h2 : a 1 = 21 := by linarith [h 0, h1]
  have h3 : a 2 = 14 := by linarith [h 1, h2]
  have h4 : a 3 = 7 := by linarith [h 2, h3]
  have h6 : Nat.ceil (a 0 / 7) = 4 := by
    rw [h1]
    norm_num [Nat.ceil_eq_iff]
  rw [h6]
  norm_num [Finset.sum_range_succ, h1, h2, h3, h4]
  <;> try linarith [h 3, h4]
  <;> try linarith
  <;> try norm_num
  <;> try linarith
  <;> try norm_num