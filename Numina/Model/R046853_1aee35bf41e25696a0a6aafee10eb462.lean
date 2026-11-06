import Mathlib

open Finset Real

theorem algebra_266303 {a : ℕ → ℝ} (ha : ∀ n, a n = 1536 * (-1 / 2) ^ n)
    (P : ℕ → ℝ) (hP : ∀ n, P n = ∏ i ∈ range n, a i) :
    IsGreatest {x | ∃ n, x = P n ∧ n ≤ 12} (P 12) := by
  constructor
  · -- Show that P 12 is in the set {x | ∃ n, x = P n ∧ n ≤ 12}
    use 12
    all_goals norm_num
  · -- Show that P 12 is the greatest in the set
    intro x hx
    rcases hx with ⟨n, rfl, hn⟩
    interval_cases n <;> norm_num [hP, ha, prod_range_succ] at *
    <;> norm_num
    <;> all_goals
      linarith