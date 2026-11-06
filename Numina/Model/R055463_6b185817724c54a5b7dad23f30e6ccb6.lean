import Mathlib

theorem number_theory_128277 (a b c : ℕ) (ha : a = 10) (hb : b = 15) (hc : c = 14) :
    lcm (lcm a b) c = 210 := by 
  rw [ha, hb, hc]
  rfl