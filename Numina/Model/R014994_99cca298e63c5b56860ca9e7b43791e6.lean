import Mathlib

theorem algebra_178455 (v : ℝ) (h : v > 0) :
    (1 / v - 1 / 5) * (1 / v - 1 / 15) < 0 ↔ 5 < v ∧ v < 15 := by
  constructor
  · -- Assume (1 / v - 1 / 5) * (1 / v - 1 / 15) < 0 prove 5 < v ∧ v < 15
    intro h1
    have h2 : v > 0 := h
    have h3 : (1 / v - 1 / 5) * (1 / v - 1 / 15) < 0 := by linarith
    cases mul_neg_iff.mp h3 with
    | inl h4 =>
      -- Contradicts because it would require v < 5 and v > 15
      have h4' : v < (5 : ℝ) := by
        have h4a : 1 / v - 1 / 5 > 0 := by linarith [h4.left]
        have h4b : 1 / v > 1 / 5 := by linarith
        by_contra h5
        push_neg at h5
        have h6 : v ≥ 5 := by nlinarith
        have h7 : 1 / v ≤ 1 / 5 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      have h4'' : v > (15 : ℝ) := by
        have h4c : 1 / v - 1 / 15 < 0 := by linarith [h4.right]
        have h4d : 1 / v < 1 / 15 := by linarith
        by_contra h5
        push_neg at h5
        have h6 : v ≤ (15 : ℝ) := by linarith
        have h7 : 1 / v ≥ 1 / 15 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      linarith
    | inr h4 =>
      -- This direction works: we prove 5 < v < 15
      have h5 : v > (5 : ℝ) := by
        have h4a : 1 / v - 1 / 5 < 0 := by linarith [h4.left]
        have h4b : 1 / v < 1 / 5 := by linarith
        by_contra h5
        push_neg at h5
        have h6 : v ≤ (5 : ℝ) := by linarith
        have h7 : 1 / v ≥ 1 / 5 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      have h6 : v < (15 : ℝ) := by
        have h4a : 1 / v - 1 / 15 > 0 := by linarith [h4.right]
        have h4b : 1 / v > 1 / 15 := by linarith
        by_contra h5
        push_neg at h5
        have h6 : v ≥ 15 := by linarith
        have h7 : 1 / v ≤ 1 / 15 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      constructor
      · linarith
      · linarith
  · -- Assume 5 < v ∧ v < 15 prove (1 / v - 1 / 5) * (1 / v - 1 / 15) < 0
    rintro ⟨h1, h2⟩
    have h3 : 1 / v - 1 / 5 < 0 := by
      have h4 : v > (5 : ℝ) := by linarith
      have h4' : 1 / v < 1 / 5 := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      linarith
    have h4 : 1 / v - 1 / 15 > 0 := by
      have h5 : v < (15 : ℝ) := by linarith
      have h6 : 1 / v > 1 / 15 := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      linarith
    have h5 : (1 / v - 1 / 5) * (1 / v - 1 / 15) < (0 : ℝ) := by
      nlinarith
    linarith