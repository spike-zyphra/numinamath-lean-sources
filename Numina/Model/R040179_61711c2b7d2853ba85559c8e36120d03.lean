import Mathlib

theorem algebra_204381 {x y : ℝ} (h₀ : |y - x| - |x| / x + 1 = 0) (h₁ : |2 * x - y| + |x + y - 1| + |x - y| + y - 1 = 0) (hx : x ≠ 0) :
    0 < x ∧ x = y ∧ y ≤ 0.5 := by
  have h2 : x > 0 := by
    by_cases h3 : x > 0
    · -- Assume x > 0
      have h4 : |x| = x := abs_of_pos h3
      have h5 : |x| / x = 1 := by
        rw [h4]
        field_simp [show x ≠ 0 by assumption]
      have eq1 := h₀
      have h6 : |y - x| = 0 := by
        have h7 : |y - x| - |x| / x + 1 = 0 := h₀
        rw [h5] at h7
        linarith
      have h7 : y = x := by
        rw [abs_eq_zero] at h6
        linarith
      -- Now check equation 2
      have h10 : |2 * x - y| + |x + y - 1| + |x - y| + y - 1 = 0 := h₁
      rw [show y = x by linarith [h7]] at h10
      -- Now check equation 2
      have eq2 : |(2 * x - x)| + |(x + x - 1)| + |(x - x)| + x - 1 = 0 := by linarith
      have h11 : |(2 * x - x)| = |x| := by
        have h12 : (2 * x - x) = x := by
          linarith
        rw [h12]
      have h12 : |x| = x := abs_of_pos h3
      have h13 : |(2 * x - x)| = x := by
        rw [h11, h12]
      have h14 : |(x + x - 1)| = |(2 * x - 1)| := by
        have h15 : x + x - 1 = 2 * x - 1 := by
          linarith
        rw [h15]
      have h15 : |(x - x)| = 0 := by
        norm_num
      rw [h13, h14, h15] at eq2
      by_cases h4 : 2 * x - 1 ≥ 0
      · -- Assume 2x - 1 ≥ 0, so x ≥ 0.5
        have h16 : |(2 * x - 1)| = (2 * x - 1) := abs_of_nonneg h4
        rw [h16] at eq2
        nlinarith
      · -- Assume 2x - 1 < 0, so x < 0.5
        have h18 : |(2 * x - 1)| = -(2 * x - 1) := abs_of_neg (by linarith)
        rw [h18] at eq2
        nlinarith
    · -- Assume x ≤ 0
      have h4 : x < 0 := by
        by_contra h5
        push_neg at h5
        have h6 : x = 0 := by linarith
        contradiction
      have h4' : |x| = -x := abs_of_neg h4
      have h5 : |x| / x = -1 := by
        rw [h4']
        field_simp [show x ≠ 0 by assumption]
      have eq1 := h₀
      have h6 : |y - x| = -2 := by
        have h7 : |y - x| - |x| / x + 1 = 0 := h₀
        rw [h5] at h7
        linarith
      have h6' : |y - x| ≥ 0 := abs_nonneg (y - x)
      linarith
  -- x > 0 has been proved.
  have h3 : x > 0 := h2
  have h4 : |x| = x := abs_of_pos h3
  have h5 : |x| / x = 1 := by
    rw [h4]
    field_simp [show x ≠ 0 by assumption]
  have eq1 := h₀
  have h6 : |y - x| = 0 := by
    have h7 : |y - x| - |x| / x + 1 = 0 := h₀
    rw [h5] at h7
    linarith
  have h7 : y = x := by
    rw [abs_eq_zero] at h6
    linarith
  have h9 : x = y := by linarith [h7]
  -- Now check equation 2
  have h10 : |2 * x - y| + |x + y - 1| + |x - y| + y - 1 = 0 := h₁
  rw [show y = x by linarith [h7]] at h10
  -- Now check equation 2
  have eq2 : |(2 * x - x)| + |(x + x - 1)| + |(x - x)| + x - 1 = 0 := by linarith
  have h11 : |(2 * x - x)| = |x| := by
    have h12 : (2 * x - x) = x := by
      linarith
    rw [h12]
  have h12 : |x| = x := abs_of_pos h3
  have h13 : |(2 * x - x)| = x := by
    rw [h11, h12]
  have h14 : |(x + x - 1)| = |(2 * x - 1)| := by
    have h15 : x + x - 1 = 2 * x - 1 := by
      linarith
    rw [h15]
  have h15 : |(x - x)| = 0 := by
    norm_num
  rw [h13, h14, h15] at eq2
  constructor
  · linarith
  constructor
  · linarith
  · -- Show y ≤ 0.5
    rw [show y = x by linarith [h7]]
    by_cases h4 : 2 * x - 1 ≥ 0
    · -- Assume 2x - 1 ≥ 0, so x ≥ 0.5
      have h16 : |(2 * x - 1)| = (2 * x - 1) := abs_of_nonneg h4
      rw [h16] at eq2
      nlinarith
    · -- Assume 2x - 1 < 0, so x < 0.5
      have h18 : |(2 * x - 1)| = -(2 * x - 1) := abs_of_neg (by linarith)
      rw [h18] at eq2
      nlinarith