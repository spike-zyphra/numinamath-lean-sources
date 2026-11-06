import Mathlib

theorem algebra_215800 (x : ℝ) (hx : 0.9 < x ∧ x < 1.0) :
    x < (x ^ (x ^ x)) ∧ (x ^ (x ^ x)) < (x ^ x) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 < x := by
    linarith
  have h2 : x < 1 := by
    norm_num at hx2 ⊢
    linarith
  have h5 : x ^ x > x := by
    have h5 : x ^ x > x ^ (1 : ℝ) := by
      have h7 : x < (1 : ℝ) := h2
      have h8 : x > 0 := h1
      have h9 : x < (1 : ℝ) := h2
      have h10 : x ^ x > x ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals
          nlinarith
      linarith
    have h6 : x ^ (1 : ℝ) = x := by
      simp
    rw [h6] at h5
    linarith
  have h7 : x ^ x < (1 : ℝ) := by
    have h8 : x < (1 : ℝ) := h2
    have h9 : x > 0 := h1
    have h10 : x ^ x < (1 : ℝ) := by
      have h11 : x ^ x < (x ^ (0 : ℝ) ) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals
          nlinarith
      have h12 : x ^ (0 : ℝ) = 1 := by
        simp
      rw [h12] at h11
      linarith
    linarith
  have h11 : x < (x ^ (x ^ x)) := by
    have h12 : x ^ (x ^ x) > x := by
      have h13 : x ^ (x ^ x) > x ^ (1 : ℝ) := by
        have h14 : x ^ x < (1 : ℝ) := h7
        have h15 : x ^ x > 0 := by positivity
        have h16 : x < (1 : ℝ) := h2
        have h17 : x > 0 := h1
        have h18 : x ^ (x ^ x) > x ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals
            nlinarith
        linarith
      have h18 : x ^ (1 : ℝ) = x := by
        simp
      rw [h18] at h13
      linarith
    linarith
  have h12 : (x ^ (x ^ x)) < (x ^ x) := by
    have h13 : x ^ (x ^ x) < x ^ x := by
      have h14 : x ^ x > x := h5
      have h15 : x ^ x > 0 := by positivity
      have h16 : x < (1 : ℝ) := h2
      have h17 : x > 0 := h1
      have h18 : x ^ (x ^ x) < x ^ x := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals
          nlinarith
      linarith
    linarith
  constructor
  · exact h11
  · exact h12