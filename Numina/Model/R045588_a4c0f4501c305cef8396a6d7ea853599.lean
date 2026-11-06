import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_288693 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ t = min x (y / (x ^ 2 + y ^ 2))} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt(2)/2 is in the set
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    · -- Show sqrt(2)/2 = min x (y / (x^2 + y^2))
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by linarith)
      have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 + (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h1]
      have h4 : min (Real.sqrt 2 / 2 : ℝ) ((Real.sqrt 2 / 2) / ((Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2)) = Real.sqrt 2 / 2 := by
        have h5 : (Real.sqrt 2 / 2 : ℝ) / ((Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2) = Real.sqrt 2 / 2 := by
          have h6 : (Real.sqrt 2 / 2 : ℝ) ^ 2 + (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 := h3
          rw [h6]
          field_simp
          <;> nlinarith
        rw [h5]
        apply min_eq_left
        all_goals nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [h4]
  · -- Show that sqrt(2)/2 is greatest
    intro t ht
    rcases ht with ⟨x, y, hx, hy, ht⟩
    by_contra h
    push_neg at h
    have h1 : t = min x (y / (x ^ 2 + y ^ 2)) := by
      linarith [ht]
    have h2 : x > Real.sqrt 2 / 2 := by
      by_contra h3
      push_neg at h3
      have h4 : min x (y / (x ^ 2 + y ^ 2)) ≤ Real.sqrt 2 / 2 := by
        cases min_cases x (y / (x ^ 2 + y ^ 2)) with
        | inl h5 =>
          nlinarith [h3, Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
        | inr h5 =>
          nlinarith [h3, Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
      linarith [h1, h4, h]
    have h3 : y / (x ^ 2 + y ^ 2) > Real.sqrt 2 / 2 := by
      have h4 : min x (y / (x ^ 2 + y ^ 2)) ≤ y / (x ^ 2 + y ^ 2) := by
        cases min_cases x (y / (x ^ 2 + y ^ 2)) with
        | inl h5 =>
          nlinarith [h5]
        | inr h5 =>
          nlinarith [h5]
      linarith [h1, h4, h]
    have h6 : y > Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2) := by
      have h7 : y / (x ^ 2 + y ^ 2) > Real.sqrt 2 / 2 := h3
      apply (lt_div_iff₀ (by positivity)).mp at h7
      nlinarith
    nlinarith [sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (y - Real.sqrt 2 / 2), 
              Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
              mul_pos hx hy, sq_nonneg (x - y)]