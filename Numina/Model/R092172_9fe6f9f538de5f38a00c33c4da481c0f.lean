import Mathlib

theorem inequalities_307682 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a = 6 ∧ b = 7) → a * b ≤ (13 / 2) ^ 2 := by 
  intro ⟨ha_eq, hb_eq⟩
  rw [ha_eq, hb_eq]
  norm_num