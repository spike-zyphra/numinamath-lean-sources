import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10403 {a : ℝ} (ha : a ≠ 0) :
    (∃! x : ℝ, 2^(abs (2*x-2)) - a * cos (1 - x) = 0) ↔ a = 1 := by
  constructor
  · -- Assume there exists a unique real solution to the equation, then a = 1.
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : 2^(abs (2 * x - 2)) - a * cos (1 - x) = 0 := hx1
    have h2 : (2 ^ (abs (2 * (2 - x) - 2)) - a * cos (1 - (2 - x)) = 0) := by
      -- 2 ^ |2(2-x) - 2| - a * cos(1 - (2 - x)) = 0.
      -- Note that 2 * (2 - x) - 2 = 2 * (2 - x - 1) = 2 * (1 - x)
      -- Therefore, |2 * (2 - x) - 2| = |2 * (1 - x)| = |2 * (x - 1)| = |2 *x - 2|, since |a| = | -a|
      have h_abs : abs (2 * (2 - x) - 2) = abs (2 * x - 2) := by
        have h1 : 2 * (2 - x) - 2 = - (2 * x - 2) := by ring
        rw [h1]
        rw [abs_neg]
      -- Similarly, 1 - (2 - x) = 1 - 2 + x = x -1, so cos(1 - (2 -x))=cos(x-1). Since cos is even, cos(x-1)=cos(1 -x).
      have h_cos : cos (1 - (2 - x)) = cos (1 - x) := by
        have h1 : 1 - (2 - x) = x - 1 := by ring
        rw [h1]
        have h2 : cos (x - 1) = cos (1 - x) := by
          rw [show 1 - x = - (x - 1) by ring]
          rw [cos_neg]
        rw [h2]
      -- Therefore, using h1: 2^|2x - 2| - a * cos(1 - x) =0:
      rw [h_abs, h_cos]
      linarith [h1]
    have h3 : (2 - x) = x := by
      apply hx2 (2 - x) h2
    have hx : x = 1 := by
      linarith [h3]
    rw [hx] at h1
    have h4 : abs (2 * (1 : ℝ) - 2) = 0 := by
      norm_num [abs]
    have h5 : (2 ^ (abs (2 * (1 : ℝ) - 2)) : ℝ) = (1 : ℝ) := by
      rw [h4]
      norm_num
    have h6 : cos (1 - (1 : ℝ)) = 1 := by
      norm_num [cos_zero]
    rw [h5, h6] at h1
    linarith
  · -- Assume a =1, then there exists a unique real solution to the equation.
    intro h
    rw [h]
    use 1
    constructor
    · -- For x=1, we have 2^(abs (2 * 1 - 2)) -1 * cos (1 - 1) = 0
      norm_num [abs]
      <;> norm_num [cos_zero]
    · -- For any y such that 2^(abs (2 * y - 2)) -1 * cos (1 - y) =0, we must have y=1
      intro y hy
      have h1 : (2 : ℝ) ^ (abs (2 * y - 2)) - (1 : ℝ) * cos (1 - y) = 0 := by
        simpa using hy
      by_cases h3 : y = 1
      · -- If y = 1, it's the same as our solution
        norm_num [h3]
      · -- Assume y ≠1
        have h2 : y ≠ 1 := h3
        have hneq : abs (2 * y - 2) ≠ 0 := by
          by_contra hneq
          have : abs (2 * y - 2) = 0 := by linarith [hneq]
          have : y = 1 := by
            rw [abs_eq_zero] at this
            linarith [this]
          contradiction
        have h3 : abs (2 * y - 2) > 0 := by
          by_contra h3
          have : abs (2 * y - 2) ≤ 0 := by linarith [h3]
          have : abs (2 * y - 2) = 0 := by linarith [abs_nonneg (2 * y - 2), this]
          contradiction
        have h4 : (2 : ℝ) ^ (abs (2 * y - 2)) > (1 : ℝ) := by
          have h5 : abs (2 * y - 2) > (0 : ℝ) := h3
          have h6 : (2 : ℝ) ^ (abs (2 * y - 2)) > (2 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          have h7 : (2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
            simp
          linarith [h6, h7]
        have h5 : cos (1 - y) < (1 : ℝ) := by
          have h6 : 1 - y ≠ 0 := by
            by_contra h
            have : y = 1 := by linarith [h]
            contradiction
          have h7 : cos (1 - y) < (1 : ℝ) := by
            have h8 : cos (1 - y) ≤ (1 : ℝ) := by
              apply cos_le_one
            by_contra h
            push_neg at h
            have h9 : cos (1 - y) = (1 : ℝ) := by
              linarith [h, h8]
            have h10 : 1 - y = 0 := by
              have h11 : cos (1 - y) = 1 := by
                linarith [h9]
              rw [cos_eq_one_iff] at h11
              rcases h11 with ⟨k, hk⟩
              have : (1 - y) = (0 : ℝ) := by
                linarith [hk]
              linarith
            have h7 : y = 1 := by linarith [h10]
            contradiction
          linarith [h7]
        -- Contradicts: left side is >1 and right side <1, so equation cannot hold.
        nlinarith [abs_nonneg (2 * y - 2), h4, h5, Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (abs (2 * y - 2) ) ]