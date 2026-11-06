import Mathlib

/- Show that every common multiple of the positive integers \( a \) and \( b \) is divisible by the least common multiple of \( a \) and \( b \).-/
theorem number_theory_4579 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (habm : a ∣ m ∧ b ∣ m) :
    Nat.lcm a b ∣ m := by
  -- exact `lcm_dvd` in Mathlib
  apply lcm_dvd;exact habm.1;exact habm.2
