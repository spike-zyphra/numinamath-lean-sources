import Mathlib

/- Given that $x$ satisfies $\frac{1}{x-3}+2<0$, find the greatest integer not greater than $x$.

 -/
theorem inequalities_3467 (x : ℝ) (hx : x ≠ 3) (h : 1 / (x - 3) + 2 < 0) :
    ⌊x⌋ = 2 := by
  have h1 : x - 3 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h2 : 1 / (x - 3) + 2 < 0 := h
  have h3 : 1 / (x - 3) < -2 := by linarith
  by_cases h4 : x - 3 > 0
  · -- Assume x - 3 > 0
    have h5 : 1 / (x - 3) < -2 := by linarith
    have h6 : (1 : ℝ) < -2 * (x - 3) := by
      have h7 : x - 3 > 0 := h4
      have h8 : 1 / (x - 3) < -2 := h5
      have h9 : (1 / (x - 3) : ℝ) * (x - 3) < (-2 : ℝ) * (x - 3) := by
        apply mul_lt_mul_of_pos_right h8 (by linarith)
      have h10 : (1 / (x - 3) : ℝ) * (x - 3) = 1 := by
        field_simp [show x - 3 ≠ 0 by assumption]
      nlinarith [h9, h10]
    nlinarith
  · -- Assume x - 3 ≤ 0
    by_cases h5 : x - 3 < 0
    · -- Assume x - 3 < 0
      have h6 : 1 / (x - 3) < -2 := by linarith
      have h7 : (1 : ℝ) > -2 * (x - 3) := by
        have h8 : x - 3 < (0 : ℝ) := h5
        have h9 : 1 / (x - 3) < (-2 : ℝ) := h6
        have h10 : (1 / (x - 3) : ℝ) * (x - 3) > (-2 : ℝ) * (x - 3) := by
          apply mul_lt_mul_of_neg_right h9 (by linarith)
        have h11 : (1 / (x - 3) : ℝ) * (x - 3) = 1 := by
          field_simp [show x - 3 ≠ 0 by intro h6; apply hx; linarith]
        nlinarith [h10, h11]
      have h8 : x > (5 : ℝ) / 2 := by nlinarith
      have h9 : x < (3 : ℝ) := by
        by_contra h9
        push_neg at h9
        have h10 : x ≥ (3 : ℝ) := by nlinarith
        have h11 : x - 3 ≥ 0 := by nlinarith
        have h8 : x - 3 < 0 := h5
        nlinarith
      have h10 : 2 ≤ x := by
          nlinarith
      have h11 : x < 3 := by
          nlinarith
      have h12 : ⌊x⌋ = 2 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact h12
    · -- Assume x - 3 ≥ 0
      have h6 : x - 3 ≥ 0 := by linarith
      have h7 : x - 3 > 0 := by
        by_contra h8
        push_neg at h8
        have h8 : x - 3 = 0 := by linarith [h8, h6]
        exfalso
        apply hx
        linarith
      have h8 : 1 / (x - 3) + 2 < 0 := h
      have h9 : 1 / (x - 3) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith
      nlinarith