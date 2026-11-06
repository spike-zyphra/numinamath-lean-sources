import Mathlib

theorem number_theory_200615 (a b c : ℕ) (ha : a = 4) (hb : b = 5) (hc : c = 6) :
    lcm (lcm a b) c = 60 := by
  rw [ha, hb, hc]
  norm_num [lcm]