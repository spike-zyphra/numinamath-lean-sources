import Mathlib

theorem algebra_2242 (a b c : ℝ) (ha : a = -1) (hb : b = 0) (hc : c = 1) :
    (a^2007 + b^2008 - c^2009) / (a^2010 - b^2011 + c^2012) = -1 := by
  rw [ha, hb, hc]
  norm_num