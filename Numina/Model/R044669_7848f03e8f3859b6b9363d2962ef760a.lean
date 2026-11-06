import Mathlib

theorem algebra_290112 (x : ℝ) (h : 1 / Real.cos (2022 * x) + Real.tan (2022 * x) = 1 / 2022) :
    1 / Real.cos (2022 * x) - Real.tan (2022 * x) = 2022 := by
  have h1 : Real.cos (2022 * x) ≠ 0 := by
    by_contra h1
    have htan : Real.tan (2022 * x) = 0 := by
      simp [Real.tan_eq_sin_div_cos, h1]
    rw [htan] at h
    field_simp [h1] at h
    all_goals
      nlinarith [Real.sin_sq_add_cos_sq (2022 * x)]
  have h2 : Real.cos (2022 * x) ^ 2 + Real.sin (2022 * x) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (2022 * x)
  have h3 : Real.tan (2022 * x) = Real.sin (2022 * x) / Real.cos (2022 * x) := by
    rw [Real.tan_eq_sin_div_cos]
  have h4 : (1 + Real.sin (2022 * x)) * 2022 = Real.cos (2022 * x) := by
    rw [h3] at h
    have h1' : Real.cos (2022 * x) ≠ 0 := h1
    field_simp [h1'] at h
    nlinarith
  have h6 : 1 / Real.cos (2022 * x) - Real.tan (2022 * x) = 2022 := by
    rw [h3]
    have h1' : Real.cos (2022 * x) ≠ 0 := h1
    have hcos : Real.cos (2022 * x) = (1 + Real.sin (2022 * x)) * 2022 := by
      linarith
    have eq1 : (Real.sin (2022 * x) - (- (2022 ^ 2) + 1) / (2022 ^ 2 + 1)) * (Real.sin (2022 * x) - (- (2022 ^ 2) - 1) / (2022 ^ 2 + 1)) = 0 := by
      rw [hcos] at h2
      field_simp at h2 ⊢
      <;> nlinarith [sq_pos_of_ne_zero (show (2022: ℝ) ≠ 0 by nlinarith), sq_nonneg (Real.sin (2022 * x) - -1), sq_nonneg (Real.sin (2022 * x) - (- (2022^2) + 1) / (2022^2 + 1))]
    cases' (mul_eq_zero.mp eq1) with h_eq h_eq2
    · -- Case where we have the correct solution.
      have eq2 : Real.sin (2022 * x) = (- (2022 ^ 2) + 1) / (2022 ^ 2 + 1) := by
        linarith
      have eq3 : Real.cos (2022 * x) = 4044 / (2022 ^ 2 + 1) := by
        rw [hcos]
        rw [eq2]
        field_simp
        <;> nlinarith
        <;> nlinarith
      have h5 : 1 / Real.cos (2022 * x) - (Real.sin (2022 * x) / Real.cos (2022 * x)) = 2022 := by
        rw [eq3, eq2]
        field_simp [h1']
        <;> ring_nf <;> nlinarith
        <;> nlinarith
      field_simp [h1'] at h5 ⊢
      nlinarith
      all_goals
        nlinarith
    · -- Case where we have a contradiction
      have eq3 : Real.sin (2022 * x) = -1 := by
        have eq4 : (Real.sin (2022 * x) - (- (2022 ^ 2) - 1) / (2022 ^ 2 + 1)) = 0 := h_eq2
        have eq5 : Real.sin (2022 * x) = (- (2022 ^ 2) - 1) / (2022 ^ 2 + 1) := by
          linarith
        rw [eq5]
        field_simp
        <;> ring_nf <;> nlinarith
      have eq4 : Real.cos (2022 * x) = 0 := by
        rw [hcos]
        rw [eq3]
        nlinarith
      contradiction
  exact h6
  all_goals
    nlinarith
  <;> nlinarith [h]
  all_goals
    nlinarith
  <;> nlinarith [h]
  all_goals
    nlinarith
  <;> nlinarith [h]
  all_goals
    nlinarith