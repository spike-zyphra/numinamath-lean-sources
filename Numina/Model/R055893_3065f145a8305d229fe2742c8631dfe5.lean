import Mathlib

theorem algebra_315655 {a : ℝ} (ha : a ≠ 0) (h : 1 / a - abs a = 1) :
    1 / a + abs a = Real.sqrt 5 := by
  by_cases h1 : a > 0
  · -- Case 1: a > 0, so |a| = a
    have h2 : abs a = a := abs_of_pos h1
    have eq1 : 1 / a - a = 1 := by 
      rw [h2] at h
      linarith
    have h3 : a^2 + a - 1 = 0 := by
      have h4 : a ≠ 0 := ha
      field_simp at eq1
      nlinarith
    have h5 : (1 / a + a)^2 = 5 := by
      have ha2 : a^2 = 1 - a := by
        nlinarith
      have h1 : 1 / a = 1 + a := by linarith [eq1]
      calc
        (1 / a + a)^2 = (1 + a + a)^2 := by rw [h1]
        _ = (1 + 2*a)^2 := by ring
        _ = 1 + 4*a + 4*a^2 := by ring
        _ = 1 + 4*a + 4*(1 - a) := by rw [ha2]
        _ = 1 + 4*a + 4 - 4*a := by ring
        _ = 5 := by ring
    have h6 : 1 / a + a > 0 := by
      have h7 : a > 0 := h1
      have h8 : 1 / a > 0 := by
        apply div_pos
        norm_num
        linarith
      have h9 : a > 0 := h1
      nlinarith [h8, h9]
    have h7 : (1 / a + a) = Real.sqrt 5 := by
      have hsq : (1 / a + a)^2 = 5 := h5
      have hpos : (1 / a + a) > 0 := h6
      have hsq5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
      have heq : (1 / a + a) = Real.sqrt 5 := by
        have h1 : (1 / a + a) > 0 := hpos
        have h2 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        have h3 : ((1 / a + a)^2 = (Real.sqrt 5)^2) := by rw [hsq, hsq5]
        have h4 : ((1 / a + a) = (Real.sqrt 5)) := by
          have h5 : (1 / a + a) ≥ 0 := by linarith
          have h6 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
          nlinarith [h3, Real.sqrt_nonneg 5, sq_nonneg (1 / a + a - Real.sqrt 5)]
        exact h4
      exact heq
    have h10 : 1 / a + abs a = 1 / a + a := by
      rw [h2]
    linarith [h7, h10]
  · -- Case 2: a ≤ 0, so |a| = -a
    have h2 : abs a = -a := abs_of_nonpos (show a ≤ 0 by
      by_contra h2
      push_neg at h2
      linarith [h1]
    )
    have eq1 : 1 / a + a = 1 := by
      rw [h2] at h
      field_simp at h ⊢
      nlinarith
    have h4 : a^2 - a + 1 = 0 := by
      have h4 : a ≠ 0 := ha
      field_simp at eq1
      nlinarith
    have h5 : a^2 - a + 1 > 0 := by
      nlinarith [sq_nonneg (a - 1 / 2)]
    have h6 : a^2 - a + 1 = 0 := by linarith [h4]
    nlinarith [h5, h6]