import Mathlib

open Matrix

theorem calculus_21976
    (a b c : Fin 3 → ℝ)
    (ha : a 0 = 2 ∧ a 1 = 1 ∧ a 2 = 0)
    (hb : b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 1)
    (hc : c 0 = 1 ∧ c 1 = -2 ∧ c 2 = -3) :
    crossProduct (crossProduct a b) c - crossProduct a (crossProduct b c) =
    ![6, 3, 0] := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  rcases hc with ⟨hc0, hc1, hc2⟩
  funext i
  fin_cases i <;> simp [crossProduct, ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2]
  <;> norm_num [ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2]