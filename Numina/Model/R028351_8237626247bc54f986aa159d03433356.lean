import Mathlib

theorem algebra_20934 (a : Fin 20 → ℝ) (b : Fin 30 → ℝ) (ha : ∑ i, a i / 20 = 30) (hb : ∑ i, b i / 30 = 20) :
    (∑ i, a i + ∑ i, b i) / 50 = 24 := by
  have h1 : ∑ i, a i = 600 := by
    have eq1 : ∑ i, a i / 20 = (∑ i, a i) / 20 := by 
      rw [Finset.sum_div]
    rw [eq1] at ha
    linarith
  have h2 : ∑ i, b i = 600 := by
    have eq2 : ∑ i, b i / 30 = (∑ i, b i) / 30 := by 
      rw [Finset.sum_div]
    rw [eq2] at hb
    linarith
  rw [h1, h2]
  norm_num