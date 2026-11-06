import Mathlib

theorem algebra_16830 {A B C : ℝ}
    (hA : A = (2006 / 2005 : ℝ) + 2006 / 2007)
    (hB : B = 2006 / 2007 + 2008 / 2007)
    (hC : C = 2007 / 2006 + 2007 / 2008) :
    A > B ∧ A > C := by
  rw [hA, hB, hC]
  constructor
  · -- Show that A > B
    norm_num
  · -- Show that A > C
    norm_num