import Mathlib

open Real

theorem algebra_312854 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a < 1) (h' : b < 1) (h'' : c < 1) (h''' : 0 < c) (h'''' : c < b) (h''''' : b < a)
    (f : ℝ → ℝ) (hf : f = fun x => logb (1 / 2) x) (x y z : ℝ)
    (hx : x = a / f a) (hy : y = b / f b) (hz : z = c / f c) :
    x > y ∧ y > z := by
  have hfa : f a = logb (1 / 2) a := by rw [hf]
  have hfb : f b = logb (1 / 2) b := by rw [hf]
  have hfc : f c = logb (1 / 2) c := by rw [hf]
  rw [hx, hfa]
  rw [hy, hfb]
  rw [hz, hfc]
  have h1 : logb (1 / 2) a > 0 := by
    have h4 : logb (1 / 2) a > logb (1 / 2) 1 := by
      apply Real.logb_lt_logb_of_base_lt_one
      all_goals
        linarith
    have h5 : logb (1 / 2) 1 = 0 := by
      norm_num [logb_one]
    linarith
  have h2 : logb (1 / 2) b > 0 := by
    have h4 : logb (1 / 2) b > logb (1 / 2) 1 := by
      apply Real.logb_lt_logb_of_base_lt_one
      all_goals
        linarith
    have h5 : logb (1 / 2) 1 = 0 := by
      norm_num [logb_one]
    linarith
  have h3 : logb (1 / 2) c > 0 := by
    have h4 : logb (1 / 2) c > logb (1 / 2) 1 := by
      apply Real.logb_lt_logb_of_base_lt_one
      all_goals
        linarith
    have h5 : logb (1 / 2) 1 = 0 := by
      norm_num [logb_one]
    linarith
  have h4 : logb (1 / 2) a < logb (1 / 2) b := by
    apply Real.logb_lt_logb_of_base_lt_one
    all_goals
      linarith
  have h5 : logb (1 / 2) b < logb (1 / 2) c := by
    apply Real.logb_lt_logb_of_base_lt_one
    all_goals
      linarith
  constructor
  · -- Show x > y
    apply (div_lt_div_iff (by linarith) (by linarith)).mpr
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Show y > z
    apply (div_lt_div_iff (by linarith) (by linarith)).mpr
    nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]