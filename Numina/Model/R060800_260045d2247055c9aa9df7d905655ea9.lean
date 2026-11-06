import Mathlib

theorem number_theory_164772 {a b c : ℤ} (ha : a = 3^55) (hb : b = 4^44) (hc : c = 5^33) :
    c < a ∧ a < b := by 
  rw [ha, hb, hc]
  constructor
  · -- Show that 5^33 < 3^55
    norm_num
  · -- Show that 3^55 < 4^44
    norm_num