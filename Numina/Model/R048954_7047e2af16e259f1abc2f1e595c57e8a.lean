import Mathlib

theorem algebra_238172 (d t1 t2 : ℝ) (ht1 : t1 = d / 60) (ht2 : t2 = d / 40)
    (hd : d > 0) (ht : t1 > 0 ∧ t2 > 0) :
    (2 * d) / (t1 + t2) = 48 := by 
  have hsum : t1 + t2 = d / 24 := by
    rw [ht1, ht2]
    ring_nf
  have h1 : d ≠ 0 := by linarith
  rw [hsum]
  field_simp
  <;> linarith