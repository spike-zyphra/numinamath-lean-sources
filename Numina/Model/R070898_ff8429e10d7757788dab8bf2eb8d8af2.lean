import Mathlib

theorem number_theory_234634 (a b c : ℕ) (ha : a = 120) (hb : b = 80) (hc : c = 100) :
    Nat.lcm (Nat.lcm a b) c = 1200 := by 
  rw [ha, hb, hc]
  norm_num [Nat.lcm]