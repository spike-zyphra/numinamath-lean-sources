import Mathlib

theorem algebra_127317 (d t1 t2 : ℝ) (ht1 : t1 = d / 30000) (ht2 : t2 = d / 20000)
    (hd : d > 0) : (2 * d) / (t1 + t2) = 24000 := by 
  rw [ht1, ht2]
  have h1 : d ≠ 0 := by linarith
  field_simp
  <;> ring_nf <;> linarith