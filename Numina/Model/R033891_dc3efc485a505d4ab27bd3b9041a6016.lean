import Mathlib

  theorem algebra_7924 {x : ℝ} (hx : (2012 - x) / 2011 + (x - 2014) / 2013 = (2016 - x) / 2015 + (x - 2018) / 2017) :
  0 < x ∧ x < 2012 := by 
    constructor
    · -- Prove that $0 < x$
      linarith
    · -- Prove that $x < 2012$
      linarith