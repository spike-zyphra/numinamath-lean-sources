import Mathlib

theorem algebra_95772 (a : Fin 20 → ℝ) (b : Fin 30 → ℝ) (ha : ∑ i : Fin 20, a i = 600)
(hb : ∑ i : Fin 30, b i = 600) :
((∑ i : Fin 20, a i) + (∑ i : Fin 30, b i)) / 50 = 24 := by
  rw [ha, hb]
  norm_num