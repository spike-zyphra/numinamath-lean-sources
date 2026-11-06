import Mathlib

theorem algebra_97285 
  (a b : Fin 20 → ℝ) 
  (ha : ∑ i, a i = 30 * 20) 
  (hb : ∑ i, b i = 20 * 30) : 
  (∑ i, a i + ∑ i, b i) / 50 = 24 := 
by
  rw [ha, hb]
  norm_num