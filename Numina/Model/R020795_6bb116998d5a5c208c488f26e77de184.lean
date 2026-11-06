import Mathlib

/- Calculate: $\frac{\sqrt{1997}}{(\sqrt{1997}-\sqrt{1999})(\sqrt{1997}-\sqrt{2001})}+\frac{\sqrt{1999}}{(\sqrt{1999}-\sqrt{2001})(\sqrt{1999}-\sqrt{1997})}+$\frac{\sqrt{2001}}{(\sqrt{2001}-\sqrt{1997})(\sqrt{2001}-\sqrt{1999})}=$ ___          ___. -/
theorem algebra_2666 {x y z : ℝ} (hx : x = Real.sqrt 1997) (hy : y = Real.sqrt 1999) (hz : z = Real.sqrt 2001) :
    x / ((x - Real.sqrt 1999) * (x - Real.sqrt 2001)) +
    y / ((y - Real.sqrt 2001) * (y - Real.sqrt 1997)) +
    z / ((z - Real.sqrt 1997) * (z - Real.sqrt 1999)) = 0 := by 
  rw [hx, hy, hz]
  have h1 : Real.sqrt 1997 > 0 := by positivity
  have h2 : Real.sqrt 1999 > 0 := by positivity
  have h3 : Real.sqrt 2001 > 0 := by positivity
  -- have h7 : Real.sqrt 1997 < Real.sqrt 1999 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- have h8 : Real.sqrt 1997 < Real.sqrt 2001 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- have h9 : Real.sqrt 1999 < Real.sqrt 2001 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hx1 : Real.sqrt 1997 ^ 2 = 1997 := Real.sq_sqrt (by norm_num)
  have hy1 : Real.sqrt 1999 ^ 2 = 1999 := Real.sq_sqrt (by norm_num)
  have hz1 : Real.sqrt 2001 ^ 2 = 2001 := Real.sq_sqrt (by norm_num)
  field_simp [(show (Real.sqrt 1997 - Real.sqrt 1999) * (Real.sqrt 1997 - Real.sqrt 2001) ≠ 0 by
    apply mul_ne_zero
    · -- Show Real.sqrt 1997 - Real.sqrt 1999 ≠ 0
      nlinarith [Real.sqrt_nonneg 1997, Real.sqrt_nonneg 1999, sq_pos_of_pos (show Real.sqrt 1997 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 1999 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1997 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1999 : ℝ) by norm_num)]
    · -- Show Real.sqrt 1997 - Real.sqrt 2001 ≠ 0
      nlinarith [Real.sqrt_nonneg 1997, Real.sqrt_nonneg 2001, sq_pos_of_pos (show Real.sqrt 1997 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 2001 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1997 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2001 : ℝ) by norm_num)]
  ), (show (Real.sqrt 1999 - Real.sqrt 2001) * (Real.sqrt 1999 - Real.sqrt 1997) ≠ 0 by
    apply mul_ne_zero
    · -- Show Real.sqrt 1999 - Real.sqrt 2001 ≠ 0
      nlinarith [Real.sqrt_nonneg 1999, Real.sqrt_nonneg 2001, sq_pos_of_pos (show Real.sqrt 1999 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 2001 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1999 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2001 : ℝ) by norm_num)]
    · -- Show Real.sqrt 1999 - Real.sqrt 1997 ≠ 0
      nlinarith [Real.sqrt_nonneg 1999, Real.sqrt_nonneg 1997, sq_pos_of_pos (show Real.sqrt 1999 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 1997 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (1999 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1997 : ℝ) by norm_num)]
  ), (show (Real.sqrt 2001 - Real.sqrt 1997) * (Real.sqrt 2001 - Real.sqrt 1999) ≠ 0 by
    apply mul_ne_zero
    · -- Show Real.sqrt 2001 - Real.sqrt 1997 ≠ 0
      nlinarith [Real.sqrt_nonneg 2001, Real.sqrt_nonneg 1997, sq_pos_of_pos (show Real.sqrt 2001 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 1997 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2001 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1997 : ℝ) by norm_num)]
    · -- Show Real.sqrt 2001 - Real.sqrt 1999 ≠ 0
      nlinarith [Real.sqrt_nonneg 2001, Real.sqrt_nonneg 1999, sq_pos_of_pos (show Real.sqrt 2001 > 0 by positivity), sq_pos_of_pos (show Real.sqrt 1999 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2001 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1999 : ℝ) by norm_num)]
  )]
  <;> nlinarith [Real.sqrt_nonneg 1997, Real.sqrt_nonneg 1999, Real.sqrt_nonneg 2001, Real.sq_sqrt (show (0 : ℝ) ≤ (1997 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (1999 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2001 : ℝ) by norm_num)]