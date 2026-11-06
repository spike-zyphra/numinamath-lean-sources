import Mathlib

theorem algebra_153835 (x y : ℝ) (hy : y ∈ Set.Icc 0 (Real.pi / 2)) (h1 : x + Real.sin y = 2008) (h2 : x + 2008 * Real.cos y = 2007) :
    x + y = 2007 + Real.pi / 2 := by
  rcases hy with ⟨hy1, hy2⟩
  have eq1 : Real.sin y - 2008 * Real.cos y = 1 := by
    linarith
  have h3 : Real.sin y ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_gt_three, hy1, hy2]
    linarith [Real.pi_gt_three, Real.pi_pos, hy2]
  have h5 : Real.sin y ≤ 1 := by
    apply Real.sin_le_one
  have h7 : Real.cos y ≥ 0 := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    all_goals linarith [Real.pi_pos, hy1, hy2]
  have h8 : Real.cos y = 0 := by
    nlinarith [eq1, Real.sin_sq_add_cos_sq y, h3, h5, h7]
  have h9 : Real.sin y = 1 := by
    have h10 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    rw [h8] at h10
    have h11 : Real.sin y ^ 2 = 1 := by nlinarith
    have h12 : Real.sin y = 1 ∨ Real.sin y = -1 := by
      rw [sq_eq_one_iff] at h11
      exact h11
    cases h12 with
    | inl h => exact h
    | inr h =>
      linarith [h3, h]
  have h10 : x = 2007 := by
    linarith [h1, h9]
  have h11 : y = Real.pi / 2 := by
    have h12 : Real.sin y = 1 := h9
    have h13 : Real.cos y = 0 := h8
    have h14 : y = Real.pi / 2 := by
      have h15 : y ≤ Real.pi / 2 := by linarith [hy2]
      by_cases h19 : y < Real.pi / 2
      · -- Assume y < π/2
        have h20 : Real.sin y < (Real.sin (Real.pi / 2) : ℝ) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_gt_three, Real.pi_pos, hy1, hy2, h19]
        have h21 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
        linarith [h21, h20, h12]
      have h20 : y ≥ Real.pi / 2 := by linarith [Real.pi_pos, Real.pi_gt_three, show y ≥ Real.pi / 2 by linarith [Real.pi_gt_three, Real.pi_pos, hy1, hy2, show y ≥ 0 by linarith]]
      have h21 : y = Real.pi / 2 := by linarith [h20, hy2]
      exact h21
    exact h14
  linarith [h10, h11, Real.pi_pos]