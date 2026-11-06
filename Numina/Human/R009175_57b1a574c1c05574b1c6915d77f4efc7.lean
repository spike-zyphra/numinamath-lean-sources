import Mathlib

theorem algebra_160453 {a : ℕ → ℤ} (h₀ : ∀ k ≥ 1, a k > 0) (ha : ∀ k, 3 ≤ k → a k = 3 * a (k - 1) - 2 * a (k - 2))
    (ha1 : a 1 ≥ 1) (ha2 : a 2 > a 1) :
    ∀ k, 2 ≤ k → a k > 2 ^ (k - 2) := by
  have H (n : ℕ) (hn : 2 ≤ n) : (a (n + 1) - a n : ℤ) = 2 * (a n - a (n - 1)) := by
    specialize ha (n + 1) (by omega)
    rw [show n + 1 - 1 = n by omega, show n + 1 - 2 = n - 1 by omega] at ha
    linear_combination ha
  have H (n : ℕ) (hn : 2 ≤ n) : (a n - a (n - 1) : ℤ) = 2 ^ (n - 2) * (a 2 - a 1) := by
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num
    | succ n hn ih =>
      rw [show n + 1 - 1 = n by omega, H n hn, ih,
          show n + 1 - 2 = n - 2 + 1 by omega]
      ring
  intro n hn
  calc a n
    _ = (a n - a (n - 1)) + a (n - 1) := by ring
    _ = 2 ^ (n - 2) * (a 2 - a 1) + a (n - 1) := by rw [H n hn]
    _ > 2 ^ (n - 2) * (a 2 - a 1) := by linarith only [h₀ (n - 1) (by omega)]
    _ ≥ 2 ^ (n - 2) := by nlinarith only [ha2, show 2 ^ (n - 2) > 0 by positivity]
