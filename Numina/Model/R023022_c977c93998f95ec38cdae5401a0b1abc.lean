import Mathlib

theorem algebra_298152 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : (x + y) / 2 = 2 * Real.sqrt 3) (h2 : Real.sqrt (x * y) = Real.sqrt 3) :
    max x y - min x y = 6 := by

  have h3 : x + y = 4 * Real.sqrt 3 := by 
    linarith

  have h4 : 0 ≤ x * y := by 
    nlinarith

  have h5 : Real.sqrt (x * y) ^ 2 = Real.sqrt 3 ^ 2 := by 
    rw [h2]

  have h6 : Real.sqrt (x * y) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    nlinarith

  have h7 : Real.sqrt 3 ^ 2 = 3 := by 
    rw [Real.sq_sqrt]
    all_goals norm_num

  rw [h6, h7] at h5
  have h8 : x * y = 3 := by 
    linarith

  have h9 : (x+y)^2 = 48 := by
    calc
      (x + y) ^ 2 = (4 * Real.sqrt 3) ^ 2 := by 
        rw [h3]
      _ = 16 * (Real.sqrt 3 ^ 2) := by 
        ring_nf
      _ = 16 * 3 := by 
        rw [Real.sq_sqrt]
        all_goals norm_num
      _ = 48 := by 
        norm_num

  have h10 : (x - y) ^ 2 = 36 := by
    nlinarith [h9, h8]

  have h11 : max x y - min x y = |x - y| := by 
    cases max_cases x y with
    | inl hmax =>
      cases min_cases x y with
      | inl hmin =>
        rw [show max x y = x by linarith, show min x y = x by linarith]
        have h_eq : x - y >= 0 := by nlinarith 
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      | inr hmin =>
        rw [show max x y = x by linarith, show min x y = y by linarith]
        have h_eq : x - y >= 0 := by nlinarith 
        rw [abs_of_nonneg (by nlinarith)]
        all_goals 
          nlinarith 
    | inr hmax =>
      cases min_cases x y with 
      | inl hmin =>
        rw [show max x y = y by linarith, show min x y = x by linarith]
        have h_eq : x - y <= 0 := by nlinarith 
        rw [abs_of_nonpos (by nlinarith)]
        all_goals 
          nlinarith 
      | inr hmin =>
        rw [show max x y = y by linarith, show min x y = y by linarith]
        have h_eq : x - y <= 0 := by nlinarith 
        rw [abs_of_nonpos (by nlinarith)]
        all_goals 
          nlinarith

  have h12 : |x - y| = 6 := by
    have h13 : (x - y) ^ 2 = 36 := h10
    have h14 : (x - y) ^ 2 - 36 = 0 := by linarith
    have h15 : (x - y - 6) * (x - y + 6) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h15) with h16 h17
    · -- Case where x - y - 6 = 0, so x - y = 6.
      have h18 : x - y = 6 := by linarith
      rw [h18]
      norm_num
    · -- Case where x - y + 6 = 0, so x - y = -6.
      have h18 : x - y = -6 := by linarith
      rw [h18]
      norm_num

  rw [h11]
  exact h12