import Mathlib

open Real

theorem algebra_102987 {a : ℝ} (ha : a > 2) (a_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = 1) (h_a1 : a_seq 1 = a)
    (h_an : ∀ n, a_seq (n + 1) = (a_seq n ^ 2 / a_seq (n - 1) ^ 2 - 2) * a_seq n) :
    ∀ K, ∑ i in Finset.Icc 0 K, (1 / a_seq i) < ((2 + a - sqrt (a ^ 2 - 4)) / 2) := by
  intro K
  specialize h_an 0
  simp [show a_seq (0 + 1) = a_seq 1 by simp, h_a0, h_a1] at h_an
  all_goals nlinarith