import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10539 :
    IsGreatest {s | ∃ l w : ℝ, 80 ≤ l ∧ 40 ≤ w ∧ 2*(l+w) = 300 ∧ s = l * w} 5600 := by
  constructor
  · -- Show 5600 is in the set
    use 80, 70
    norm_num
  · -- Show 5600 is greatest in the set
    intro s h
    rcases h with ⟨l, w, hl, hw, h1, h2⟩
    have h3 : l + w = 150 := by
      linarith
    have hw_eq : w = 150 - l := by
      linarith
    have h4 : l * (150 - l) ≤ 5600 := by
      nlinarith [sq_nonneg (l - 80), sq_nonneg (l - 110), sq_nonneg (l - 70), sq_nonneg (w - 40)]
    rw [hw_eq] at h2
    nlinarith