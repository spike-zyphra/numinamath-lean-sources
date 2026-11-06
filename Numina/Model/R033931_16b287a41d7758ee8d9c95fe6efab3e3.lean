import Mathlib

theorem algebra_223615 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    max (max (max (1 / x) (x ^ 2)) (x)) (Real.sqrt x) = 1 / x ∧
    min (min (min (1 / x) (x ^ 2)) (x)) (Real.sqrt x) = x ^ 2 := by
  rcases hx with ⟨hx0, hx1⟩
  have h1 : 0 < x := hx0
  have h2 : x < 1 := hx1
  have h3 : 1 / x > 1 := by
    have h4 : x < 1 := h2
    have h5 : 0 < x := h1
    apply (lt_div_iff' (by linarith)).mpr
    nlinarith
  have h4 : Real.sqrt x < (1 : ℝ) := by
    have h5 : x < 1 := h2
    have h6 : Real.sqrt x < Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h7 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h6, h7]
  have h5 : 1 / x > Real.sqrt x := by
    linarith [h3, h4]
  have h6 : 1 / x > x ^ 2 := by
    have hx1' : x < 1 := h2
    have h2' : 0 < x := h1
    have h7 : 1 / x - x ^ 2 > 0 := by
      have h7 : 0 < 1 - x ^ 3 := by
        have h7 : x ^ 3 < (1 : ℝ) := by
          have h1' : x < 1 := h2
          nlinarith [sq_pos_of_pos h1, sq_nonneg (x - 1), sq_nonneg (x), h1']
        linarith
      have h8 : (1 / x - x ^ 2) = (1 - x ^ 3) / x := by
        field_simp
        <;> ring
      rw [h8]
      apply div_pos
      linarith
      all_goals linarith
    linarith
  have h7 : 1 / x > x := by
    have hx1' : x < 1 := h2
    have h2' : 0 < x := h1
    have h8 : 1 / x - x > 0 := by
      have h8 : 0 < 1 - x ^ 2 := by
        have h7 : x ^ 2 < (1 : ℝ) := by
          nlinarith [h1]
        linarith
      have h9 : (1 / x - x) = (1 - x ^ 2) / x := by
        field_simp
        <;> ring
      rw [h9]
      apply div_pos
      linarith
      all_goals linarith
    linarith
  -- Now to prove the maximums
  have hmax1 : max (1 / x) (x ^ 2) = 1 / x := by
    apply max_eq_left
    linarith [h6]
  have hmax2 : max (max (1 / x) (x ^ 2)) x = 1 / x := by
    rw [hmax1]
    apply max_eq_left
    linarith [h7]
  have hmax3 : max (max (max (1 / x) (x ^ 2)) (x)) (Real.sqrt x) = 1 / x := by
    rw [hmax2]
    apply max_eq_left
    linarith [h5]
  -- Now for the min
  -- First, calculate x^2 < x
  have h8 : x ^ 2 < x := by
    nlinarith
  -- Now to prove x^2 < Real.sqrt x
  have h9 : x ^ 2 < Real.sqrt x := by
    have h12 : x < 1 := h2
    have h22 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x)
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_le_sqrt (show x ≤ 1 by linarith)]
  have h10 : x ^ 2 < (1 / x) := by
    linarith [h6]
  have hmin1 : min (1 / x) (x ^ 2) = x ^ 2 := by
    apply min_eq_right
    linarith [h10]
  have hmin2 : min (min (1 / x) (x ^ 2)) x = x ^ 2 := by
    rw [hmin1]
    apply min_eq_left
    linarith [h8]
  have hmin3 : min (min (min (1 / x) (x ^ 2)) (x)) (Real.sqrt x) = x ^ 2 := by
    rw [hmin2]
    apply min_eq_left
    linarith [h9]
  constructor
  · exact hmax3
  · exact hmin3