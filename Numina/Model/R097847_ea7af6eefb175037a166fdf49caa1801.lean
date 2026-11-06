import Mathlib

theorem algebra_140130 (a b c : Fin 3 → ℝ)
    (ha : a 0 = 2 ∧ a 1 = -3 ∧ a 2 = 4)
    (hb : b 0 = -5 ∧ b 1 = 1 ∧ b 2 = 6)
    (hc : c 0 = 3 ∧ c 1 = 0 ∧ c 2 = -2) :
    (a 0 + b 0 + c 0, a 1 + b 1 + c 1, a 2 + b 2 + c 2) = (0, -2, 8) := by 
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  rcases hc with ⟨hc0, hc1, hc2⟩
  simp [Prod.ext_iff, ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2]
  <;> norm_num
  <;> tauto