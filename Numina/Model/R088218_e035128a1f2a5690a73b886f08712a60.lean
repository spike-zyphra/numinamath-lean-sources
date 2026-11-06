import Mathlib

theorem other_61473 (F : ℝ) (a : ℝ) (hF : F > 0) (ha : a > 0)
    (hF1 : F = 3.05 → a = 0.095) (hF2 : F = 3.45 → a = 0.205)
    (hF3 : F = 4.05 → a = 0.295) (hF4 : F = 4.45 → a = 0.405)
    (hF5 : F = 5.05 → a = 0.495) :
    F = 4.45 → a = 0.405 := by 
  intro h
  specialize hF4 h
  tauto