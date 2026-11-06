import Mathlib

theorem number_theory_11014 : (2 ^ 1 : ZMod 13).inv + (2 ^ 2 : ZMod 13).inv + (2 ^ 3 : ZMod 13).inv + (2 ^ 4 : ZMod 13).inv + (2 ^ 5 : ZMod 13).inv + (2 ^ 6 : ZMod 13).inv = 2 := by 
  native_decide