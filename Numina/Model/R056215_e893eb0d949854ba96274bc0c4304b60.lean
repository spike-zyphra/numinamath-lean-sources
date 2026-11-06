import Mathlib

theorem algebra_195766 {a b c : ℝ}
    (ha : a = (2005 * 2006) / (2007 * 2008))
    (hb : b = (2006 * 2007) / (2008 * 2009))
    (hc : c = (2007 * 2008) / (2009 * 2010)) :
    a < b ∧ b < c := by
  have h1 : a < b := by 
    rw [ha, hb]
    norm_num 
  have h2 : b < c := by 
    rw [hb, hc]
    norm_num 
  constructor 
  exact h1 
  exact h2