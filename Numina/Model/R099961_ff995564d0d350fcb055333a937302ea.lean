import Mathlib

open Finset Real Nat

theorem algebra_599056 {a : ℕ → ℝ} {p : ℝ} (hp : p > 1)
    (ha : ∀ n, a n ≠ 0) (hsum : ∀ n, ∑ i in range n, a i = (1 - p) * p ^ n) :
    let f (n : ℕ) := (∑ i in range (n + 1), Nat.choose n i * a i) / (2 ^ n * ∑ i in range n, a i)
    f (n + 1) < (p + 1) / (2 * p) * f n ∧
    (2 * n - 1) * f n ≤ ∑ k in range (2 * n - 1), f k ∧
    ∑ k in range (2 * n - 1), f k ≤ (p + 1) / (p - 1) * (-((p + 1) / (2 * p)) ^ (2 * n - 1)) := by
  have h1 := hsum 0
  simp at h1
  nlinarith