import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_148157 (a : ℝ) :
  (∀ k ∈ Icc (-1) 1, ∀ x ∈ Ioc 0 6, 6 * log x + x ^ 2 - 8 * x + a ≤ k * x) ↔
  a ≤ 6 - 6 * log 6 := by
  constructor
  · -- First implication: if the inequality holds, then a ≤ 6 - 6 * log 6
    intro h
    have h1 := h (-1) (by norm_num) 6 (by norm_num)
    have h2 : 6 * log 6 + (6 : ℝ) ^ 2 - 8 * (6 : ℝ) + a ≤ (-1) * (6 : ℝ) := by
      simpa using h1
    nlinarith
  · -- Reverse implication: if a ≤ 6 - 6 * log 6, then the inequality holds
    intro ha k hk x hx
    have h1 : 0 < x := hx.1
    have h2 : x ≤ 6 := hx.2
    have hk1 : -1 ≤ k := hk.1
    have hk2 : k ≤ 1 := hk.2
    have h3 : log 6 ≥ log x := by
      apply Real.log_le_log
      all_goals linarith
    nlinarith [sq_nonneg (x - 6), sq_nonneg (k + 1), sq_nonneg (log x - log 6),
              Real.log_pos (show (1 : ℝ) < (6 : ℝ) by norm_num),
              Real.log_le_sub_one_of_pos (show 0 < (6 : ℝ) by norm_num),
              Real.log_le_sub_one_of_pos (show 0 < x by linarith),
              ha, h1, h2, hk1, hk2]