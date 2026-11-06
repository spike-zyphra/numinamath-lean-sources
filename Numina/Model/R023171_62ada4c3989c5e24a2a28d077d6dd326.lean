import Mathlib

open Real

theorem algebra_130771 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha' : ∀ n, 0 < a n) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i) :
    (∀ n, 0 < S n) → (∀ n, (log (S n) + log (S (n + 2))) / 2 < log (S (n + 1))) ∧
    ¬∃ c, 0 < c ∧ (∀ n, 0 < S n - c) ∧
      (∀ n, (log (S n - c) + log (S (n + 2) - c)) / 2 = log (S (n + 1) - c)) := by
  intro hS_pos
  have h1 : S 0 = 0 := by
    specialize hS 0
    simp [Finset.sum_range_zero] at hS ⊢
    all_goals linarith
  have h2 : 0 < S 0 := hS_pos 0
  linarith [h1, h2]