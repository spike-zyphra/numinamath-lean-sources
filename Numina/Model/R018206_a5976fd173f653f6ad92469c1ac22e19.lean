import Mathlib

open Real

theorem algebra_121181 {x : ℕ → ℝ}
    (hx2 : x 2 = (2 + 1 / 2) ^ (1 / 2))
    (hxn : ∀ n ≥ 3, x n = ((2 + ∑ i ∈ Finset.Icc 3 n, (i : ℝ) ^ (1 / i)) ^ (1 / 3)) ^ (1 / 2)) :
    ∀ n ≥ 3, x (n + 1) - x n < 1 / Nat.factorial n := by 
  intro n hn
  have h1 := hxn n (by linarith)
  have h2 := hxn (n + 1) (by linarith)
  rw [h1, h2]
  have h3 : Nat.factorial n > 0 := by
    apply Nat.factorial_pos
  have h4 : (1 : ℝ) / (Nat.factorial n : ℝ) > 0 := by
    positivity
  linarith [show ((2 + ∑ i in Finset.Icc 3 (n + 1), (i : ℝ) ^ (1 / i)) ^ (1 / 3) ) ^ (1 / 2) - ((2 + ∑ i in Finset.Icc 3 n, (i : ℝ) ^ (1 / i)) ^ (1 / 3)) ^ (1 / 2) < (1 : ℝ) / Nat.factorial n by 
    simp
    all_goals 
      try { linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 + ∑ i in Finset.Icc 3 (n + 1), (i : ℝ) ^ (1 / i)) by positivity) (1 / 3), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 + ∑ i in Finset.Icc 3 n, (i : ℝ) ^ (1 / i)) by positivity) (1 / 3), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 + ∑ i in Finset.Icc 3 (n + 1), (i : ℝ) ^ (1 / i)) by positivity) (1 / 2), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 + ∑ i in Finset.Icc 3 n, (i : ℝ) ^ (1 / i)) by positivity) (1 / 2)] }
  ]