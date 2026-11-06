import Mathlib

theorem algebra_179503 {n : ℕ} (hn : n ≥ 6) (h : (35 / 100 : ℝ) * n + (5 / 13 : ℝ) * (n - 6) = n) :
    n = 10 := by
  have h1 : (n : ℝ) ≥ (6 : ℝ) := by exact_mod_cast hn
  have eq1 : (n : ℝ) < (100 : ℝ) := by
    norm_num at h ⊢
    nlinarith
  have eq2 : n < 100 := by
    by_contra h2
    push_neg at h2
    have hn8 : n ≥ 100 := by
      omega
    have hn9 : (n : ℝ) ≥ (100 : ℝ) := by exact_mod_cast hn8
    nlinarith
  interval_cases n <;> norm_num at h ⊢
  <;> all_goals omega
  <;> all_goals tauto