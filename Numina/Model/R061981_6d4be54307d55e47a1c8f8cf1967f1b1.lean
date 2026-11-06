import Mathlib

theorem inequalities_603514 (a b c : ℝ) (ha : -3/4 ≤ a) (hb : -3/4 ≤ b) (hc : -3/4 ≤ c)
    (h : a+b+c=1) :
    a/(a^2+1) + b/(b^2+1) + c/(c^2+1) ≤ 9/10 := by

  have h1 : a/(a^2+1) ≤ (18/25)*a + 3/50 := by
    have h2 : a^2 + 1 > 0 := by nlinarith 
    have h3 : a/(a^2+1) - (18/25)*a - 3/50 ≤ 0 := by
      have h4 : a/(a^2+1) - (18/25)*a - 3/50 =
          (a - (18/25)*a*(a^2 + 1) - 3/50*(a^2 + 1)) / (a^2 + 1) := by
        field_simp [h2]
        ring
      rw [h4]
      have h5 : (a - (18/25)*a*(a^2 + 1) - 3/50*(a^2 + 1)) ≤ 0 := by
        nlinarith [sq_nonneg (a + 1/2), sq_nonneg (a - 1/3), sq_nonneg (a - 1/2), sq_nonneg (a + 3/4), sq_nonneg (a - 1)]
      apply div_nonpos_of_nonpos_of_nonneg h5 (by positivity)
    linarith
  
  have h2 : b/(b^2+1) ≤ (18/25)*b + 3/50 := by
    have h2 : b^2 + 1 > 0 := by nlinarith 
    have h3 : b/(b^2+1) - (18/25)*b - 3/50 ≤ 0 := by
      have h4 : b/(b^2+1) - (18/25)*b - 3/50 =
          (b - (18/25)*b*(b^2 + 1) - 3/50*(b^2 + 1)) / (b^2 + 1) := by
        field_simp [h2]
        ring
      rw [h4]
      have h5 : (b - (18/25)*b*(b^2 + 1) - 3/50*(b^2 + 1)) ≤ 0 := by
        nlinarith [sq_nonneg (b + 1/2), sq_nonneg (b - 1/3), sq_nonneg (b - 1/2), sq_nonneg (b + 3/4), sq_nonneg (b - 1)]
      apply div_nonpos_of_nonpos_of_nonneg h5 (by positivity)
    linarith

  have h3 : c/(c^2+1) ≤ (18/25)*c + 3/50 := by
    have h2 : c^2 + 1 > 0 := by nlinarith 
    have h3 : c/(c^2+1) - (18/25)*c - 3/50 ≤ 0 := by
      have h4 : c/(c^2+1) - (18/25)*c - 3/50 =
          (c - (18/25)*c*(c^2 + 1) - 3/50*(c^2 + 1)) / (c^2 + 1) := by
        field_simp [h2]
        ring
      rw [h4]
      have h5 : (c - (18/25)*c*(c^2 + 1) - 3/50*(c^2 + 1)) ≤ 0 := by
        nlinarith [sq_nonneg (c + 1/2), sq_nonneg (c - 1/3), sq_nonneg (c - 1/2), sq_nonneg (c + 3/4), sq_nonneg (c - 1)]
      apply div_nonpos_of_nonpos_of_nonneg h5 (by positivity)
    linarith

  linarith [h1, h2, h3, h]