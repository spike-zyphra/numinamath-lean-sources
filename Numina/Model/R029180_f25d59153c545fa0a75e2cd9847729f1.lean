import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314828 :
  IsLeast {z : ℝ | ∃ x y, z = 2*x - y ∧ (y - x)*(y - 18/(25*x)) ≥ 0 ∧ (x - 1)^2 + (y - 1)^2 ≤ 1} (-1) := by
  constructor
  · -- Show that -1 is in the set.
    use 2/5, 9/5
    norm_num
  · -- Show that -1 is the least element in the set
    intro z h
    rcases h with ⟨x, y, h_eq, h1, h2⟩
    by_contra h3
    push_neg at h3
    have h3' : 2 * x - y < -1 := by linarith
    by_cases hx : x > 0
    · -- Assume x > 0
      have h1' : (y - x) * (y - 18 / (25 * x)) ≥ 0 := h1
      have h4 : x * ((y - x) * (y - 18 / (25 * x))) ≥ 0 := by
        have hx_pos : x > 0 := hx
        have h12 : (y - x) * (y - 18 / (25 * x)) ≥ 0 := h1
        nlinarith
      have h5 : x * ((y - x) * (y - 18 / (25 * x))) = (y - x) * (x * y - 18/25) := by
        field_simp
        <;> ring
      rw [h5] at h4
      nlinarith [sq_nonneg (x - 2/5), sq_nonneg (y - 9/5), sq_nonneg (x - y + 1/5), sq_nonneg (x - y - 2/5),
        sq_nonneg (x - 2/5), sq_nonneg (y - 9/5),
        sq_nonneg (x * (y - 9/5)), sq_nonneg ((y - 9/5) * (y - 1)), sq_nonneg ((x - 2/5) * (x - 1)), sq_nonneg (y - 1), sq_nonneg (x - 1)]
    · -- Assume x ≤ 0
      have hx_nonpos : x ≤ 0 := by linarith
      by_cases h21 : x = 0
      · -- When x = 0
        rw [h21] at h1 h2
        norm_num at h1 h2
        all_goals
          nlinarith [sq_nonneg (y - 1)]
      · -- When x < 0
        have h11 : x < 0 := by
          by_contra h12
          push_neg at h12
          have : x = 0 := by linarith
          tauto
        have hx_neg : x < 0 := h11
        have h14 : (y - x) * (y - 18 / (25 * x)) ≥ 0 := h1
        have h19 : (y - x) * (y - 18 / (25 * x)) * (x) ≤ 0 := by
          have h19 : (y - x) * (y - 18 / (25 * x)) ≥ 0 := h1
          have : x < 0 := hx_neg
          nlinarith
        have h5 : (y - x) * (y - 18 / (25 * x)) * (x) = (y - x) * (x * y - 18/25) := by
          field_simp [(show 25 * x ≠ 0 by
            intro h0
            have : x = 0 := by
              have h11 : 25 * x = (0 : ℝ) := by linarith
              linarith
            tauto
          )]
          <;> ring
        rw [h5] at h19
        nlinarith [sq_nonneg (x - 2/5), sq_nonneg (y - 9/5), sq_nonneg (x - y + 1/5), sq_nonneg (x - y - 2/5),
          sq_nonneg (x - 2/5), sq_nonneg (y - 9/5),
          sq_nonneg (x * (y - 9/5)), sq_nonneg ((y - 9/5) * (y - 1)), sq_nonneg ((x - 2/5) * (x - 1)), sq_nonneg (y - 1), sq_nonneg (x - 1)]