import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_190748 {a b : ℕ → ℝ}
  (ha : ∀ n, a n = a 0 + 2 * n)
  (hb : ∀ n, b n = 3 * 2 ^ (n - 1))
  (h1 : ∃ n, a n = 0 ∧ b n = 0) :
  (∀ n, a n = 2 * n - 1 ∧ b n = 3 * 2 ^ (n - 1)) ∧
  (∀ n, ∏ i in Finset.Icc 2 n, a i + ∑ i in Finset.Icc 2 n, b i < 895) ∧
  (∀ t, ∀ n, |(a (2 * t) - a n) ^ 2 + (b (2 * t) - b n) ^ 2| ≤
    8 * |(∏ i in Finset.Icc 2 n, a i) + (∑ i in Finset.Icc 2 n, b i) - 895|) ↔
  t ≤ logb (6 * sqrt 3970) 2 := by

  rcases h1 with ⟨n, h1a_n, h1b_n⟩

  have h1b_n_eq : b n = 3 * (2 : ℝ) ^ (n - 1) := hb n

  rw [h1b_n_eq] at h1b_n

  have h2 : (2 : ℝ) ^ (n - 1) = 0 := by
    nlinarith

  have h3 : (2 : ℝ) ^ (n - 1) > 0 := by
    apply pow_pos
    norm_num

  linarith