import Mathlib

theorem algebra_2610 (d t1 t2 : ℝ) (ht1 : t1 = d / 4) (ht2 : t2 = d / 6) (hd : d > 0) :
    2 * d / (t1 + t2) = 4.8 := by 
  rw [ht1, ht2]
  have h1 : d / 4 + d / 6 = (5 * d) / 12 := by 
    linarith 
  rw [h1]
  have h2 : d ≠ 0 := by linarith
  field_simp [h2]
  <;> ring_nf <;> norm_num
  <;> linarith