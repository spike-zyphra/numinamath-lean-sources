import Mathlib

  theorem algebra_7924 {x : ℝ} (hx : (2012 - x) / 2011 + (x - 2014) / 2013 = (2016 - x) / 2015 + (x - 2018) / 2017) :
  0 < x ∧ x < 2012 := by
    norm_num [sub_ne_zero] at hx
    constructor
    · -- Proving 0 < x
      linarith
    · -- Proving x < 2012
      linarith