import Mathlib

theorem algebra_114088 (a b : ℕ) (f1 f2 : ℚ)
    (hf1 : f1 = (a + 125^725 : ℚ) / (a + 625^544))
    (hf2 : f2 = (b + 121^1007 : ℚ) / (b + 343^671)) :
    f1 < f2 := by
  rw [hf1, hf2]
  have h1 : (a + 125^725 : ℚ) / (a + 625^544) < 1 := by
    have h2 : (a + 125^725 : ℚ) < (a + 625^544 : ℚ) := by
      norm_num
      all_goals linarith
    have h3 : (a + 625^544 : ℚ) > 0 := by positivity
    apply (div_lt_iff (by positivity)).mpr
    linarith
  have h4 : 1 < (b + 121^1007 : ℚ) / (b + 343^671) := by
    have h5 : (b + 343^671 : ℚ) > 0 := by positivity
    have h6 : (1 : ℚ) < (b + 121^1007 : ℚ) / (b + 343^671 : ℚ) := by
      apply (lt_div_iff (by positivity)).mpr
      have h7 : (b + 121^1007 : ℚ) > (b + 343^671 : ℚ) := by
        norm_num
        all_goals linarith
      have h8 : (b + 343^671 : ℚ) > 0 := by positivity
      linarith
    linarith
  linarith