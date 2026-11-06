import Mathlib

theorem algebra_318545 {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (h : x + 1 / x = 7) :
    Real.sqrt x - 1 / Real.sqrt x = -Real.sqrt 5 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 < x := hx1
  have h2 : x < 1 := hx2
  have hx3 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.2
    linarith
  have h4 : Real.sqrt x > 0 := hx3

  have h6 : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = 5 := by
    calc
      (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = (Real.sqrt x) ^ 2 + (1 / Real.sqrt x) ^ 2 - 2 * (Real.sqrt x * (1 / Real.sqrt x)) := by
        ring
      _ = (Real.sqrt x) ^ 2 + (1 / Real.sqrt x) ^ 2 - 2 * 1 := by
        have h5 : Real.sqrt x * (1 / Real.sqrt x) = 1 := by
          have h10 : Real.sqrt x > 0 := h4
          field_simp [show Real.sqrt x ≠ 0 by linarith]
        rw [h5]
        all_goals nlinarith
      _ = x + 1 / x - 2 * 1 := by
        have h9 : (Real.sqrt x) ^ 2 = x := by
          rw [Real.sq_sqrt]
          all_goals nlinarith
        have h10 : (1 / Real.sqrt x) ^ 2 = 1 / x := by
          have h11 : Real.sqrt x > 0 := h4
          field_simp [show Real.sqrt x ≠ 0 by linarith]
          all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
        rw [h9, h10]
        <;> field_simp [show x ≠ 0 by linarith]
        all_goals nlinarith
      _ = 5 := by
        have h7 : x + 1 / x = 7 := h
        linarith [h7]

  have h_1 : Real.sqrt x < 1 := by
    have h8 : x < (1 : ℝ) := h2
    have h9 : Real.sqrt x < Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h10 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h10, h9]

  have h14 : Real.sqrt x - 1 / Real.sqrt x < (0 : ℝ) := by
    have hx3 : 0 < Real.sqrt x := h4
    have hx5 : x < (1 : ℝ) := h2
    have hx6 : 0 < Real.sqrt x := h4
    have hx7 : Real.sqrt x * Real.sqrt x = x := by
      calc
        Real.sqrt x * Real.sqrt x = (Real.sqrt x) ^ 2 := by ring
        _ = x := by
          rw [Real.sq_sqrt]
          all_goals nlinarith
    have hx8 : Real.sqrt x - 1 / Real.sqrt x = (x - 1) / Real.sqrt x := by
      field_simp [show Real.sqrt x ≠ 0 by linarith]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
      all_goals field_simp [show Real.sqrt x ≠ 0 by linarith]
      all_goals nlinarith
    rw [hx8] at *
    apply div_neg_of_neg_of_pos
    · -- Show x - 1 < 0
      linarith
    · -- Show 0 < Real.sqrt x
      linarith

  have h15 : Real.sqrt x - 1 / Real.sqrt x = -Real.sqrt 5 := by
    have h11' : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = (5 : ℝ) := h6
    have h12' : Real.sqrt (5 : ℝ) ≥ 0 := by positivity
    have h14' : Real.sqrt x - 1 / Real.sqrt x < 0 := h14
    have h13' : (Real.sqrt x - 1 / Real.sqrt x) ^ 2 = (Real.sqrt (5 : ℝ)) ^ 2 := by
      rw [h11']
      rw [Real.sq_sqrt]
      all_goals nlinarith
    have : Real.sqrt x - 1 / Real.sqrt x = -Real.sqrt (5 : ℝ) := by
      have h17 : Real.sqrt x - 1 / Real.sqrt x < 0 := h14'
      nlinarith [Real.sqrt_nonneg (5 : ℝ), sq_nonneg (Real.sqrt x - 1 / Real.sqrt x + Real.sqrt (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by nlinarith)]
    linarith
  exact h15