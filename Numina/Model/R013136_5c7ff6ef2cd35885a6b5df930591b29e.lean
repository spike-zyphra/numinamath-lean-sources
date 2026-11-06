import Mathlib

theorem algebra_7391 (x : ℝ) (h : (2000 + x) / 2010 + (2001 + x) / 2011 + (2002 + x) / 2012 + (2003 + x) / 2013 = 4) :
    x = 10 := by
  field_simp at h
  linarith