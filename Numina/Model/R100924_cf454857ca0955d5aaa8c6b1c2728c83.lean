import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_292612 {f : ℝ → ℝ} (hf : f = λ x => abs (4 * x ^ 3 - 3 * x)) :
    IsGreatest (image f (Icc (-1) 1)) 1 := by
  constructor
  · -- Show that 1 is attained
    use 1
    constructor
    · -- Show that 1 is in the interval
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f(1) = 1
      rw [hf]
      norm_num [abs]
      all_goals try { linarith }
  · -- Show that 1 is indeed greatest
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [hf]
    simp at *
    have h1 : -1 ≤ x := by linarith [hx.1, hx.2]
    have h2 : x ≤ 1 := by linarith [hx.1, hx.2]
    have h3 : -1 ≤ 4 * x ^ 3 - 3 * x := by
      nlinarith [sq_nonneg (x * x - 1 / 4), sq_nonneg (x * x - 3 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * x - 1), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    have h4 : 4 * x ^ 3 - 3 * x ≤ 1 := by
      nlinarith [sq_nonneg (x * x - 1 / 4), sq_nonneg (x * x - 3 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * x - 1), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
    all_goals try { linarith }
    all_goals try { tauto }
    <;> try { nlinarith [sq_nonneg (x * x - 1 / 4), sq_nonneg (x * x - 3 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * x - 1), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)] }
    all_goals try { norm_num }
    all_goals try { tauto }
    <;> try { nlinarith [sq_nonneg (x * x - 1 / 4), sq_nonneg (x * x - 3 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * x - 1), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)] }
    all_goals try { norm_num }
    all_goals try { tauto }
    all_goals try { nlinarith [sq_nonneg (x * x - 1 / 4), sq_nonneg (x * x - 3 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * x - 1), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1)] }