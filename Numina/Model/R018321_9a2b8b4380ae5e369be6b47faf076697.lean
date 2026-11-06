import Mathlib

theorem algebra_485 {r : ℝ} (n : ℕ) (hr : r ≠ 1) (t : ℕ → ℝ) (ht : t = fun (k : ℕ) => k * r ^ k) :
    ∑ k in Finset.Icc 1 n, k * r ^ k = (r * (n * r ^ (n + 1) - (n + 1) * r ^ n + 1)) / (1 - r) ^ 2 := by 
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by linarith)]
    rw [ih]
    field_simp [(show (1 - r : ℝ) ≠ 0 by intro h; apply hr; linarith)]
    ring