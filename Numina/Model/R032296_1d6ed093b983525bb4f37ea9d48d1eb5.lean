import Mathlib

theorem number_theory_218634 : 17 ∣ (2^(2^1989) - 1) := by 
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd]
  simp
  native_decide