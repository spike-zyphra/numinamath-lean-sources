import Mathlib

theorem number_theory_15964 : gcd 50 5005 + lcm 50 5005 = 50055 := by
  calc
    gcd 50 5005 + lcm 50 5005 = 5 + 50050 := by
      native_decide
    _ = 50055 := by
      omega