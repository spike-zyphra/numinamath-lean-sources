import Mathlib

theorem number_theory_6875 {a b c : ℕ} (ha : a = 513) (hb : b = 135) (hc : c = 3114) :
    Nat.lcm (Nat.lcm a b) c = 887490 := by
  rw [ha, hb, hc]
  norm_num [Nat.lcm]