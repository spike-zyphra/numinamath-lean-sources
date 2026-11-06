import Mathlib

theorem calculus_17108 (a b : Fin 3 → ℝ)
    (ha : a = ![3, 1, -2]) (hb : b = ![0, 2, -1]) :
    ∃ p q r, ![4, 1, -4] = p * a + q * b + r * (crossProduct a b) := by 
  use 3 / 2
  use 0
  use -1 / 6
  rw [ha, hb]
  funext i 
  fin_cases i <;> simp [crossProduct] <;> norm_num