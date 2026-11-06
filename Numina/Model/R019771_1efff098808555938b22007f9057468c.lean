import Mathlib

theorem algebra_302795 {a b c : ℝ} (ha : (2 : ℝ)^a = 5) (hb : (2 : ℝ)^b = 10) (hc : (2 : ℝ)^c = 80) :
    2006 * a - 3344 * b + 1338 * c = 2008 := by

  have ha2 : a = Real.logb (2 : ℝ) 5 := by
    rw [←ha]
    field_simp

  have hb2 : b = Real.logb (2 : ℝ) 10 := by
    rw [←hb]
    field_simp

  have hc2 : c = Real.logb (2 : ℝ) 80 := by
    rw [←hc]
    field_simp

  have h1 : Real.logb (2 : ℝ) 10 = 1 + Real.logb (2 : ℝ) 5 := by
    calc
      Real.logb (2 : ℝ) 10 = Real.logb (2 : ℝ) (2 * 5) := by norm_num
      _ = Real.logb (2 : ℝ) 2 + Real.logb (2 : ℝ) 5 := by rw [Real.logb_mul (by norm_num) (by norm_num)]
      _ = (1 : ℝ) + Real.logb (2 : ℝ) 5 := by
        have h2 : Real.logb (2 : ℝ) (2 : ℝ) = 1 := by
          norm_num [Real.logb_eq_iff_rpow_eq]
        linarith [h2]
      _ = 1 + Real.logb (2 : ℝ) 5 := by ring

  have h2 : Real.logb (2 : ℝ) 80 = 4 + Real.logb (2 : ℝ) 5 := by
    calc
      Real.logb (2 : ℝ) 80 = Real.logb (2 : ℝ) (16 * 5) := by norm_num
      _ = Real.logb (2 : ℝ) 16 + Real.logb (2 : ℝ) 5 := by rw [Real.logb_mul (by norm_num) (by norm_num)]
      _ = Real.logb (2 : ℝ) (2 ^ 4) + Real.logb (2 : ℝ) 5 := by norm_num
      _ = (4 : ℝ) + Real.logb (2 : ℝ) 5 := by
        have h3 : Real.logb (2 : ℝ) (2 ^ 4 : ℝ) = (4 : ℝ) := by
          simp [Real.logb_pow]
        linarith [h3]

  have h3 : b = 1 + a := by
    rw [hb2]
    rw [h1]
    rw [ha2]
    all_goals linarith

  have h4 : c = 4 + a := by
    rw [hc2]
    rw [h2]
    rw [ha2]
    all_goals linarith

  rw [h3, h4]
  linarith [ha2]