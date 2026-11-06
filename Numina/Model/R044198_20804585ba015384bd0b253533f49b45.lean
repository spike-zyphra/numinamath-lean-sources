import Mathlib
theorem algebra_21785 (m h v t: ℝ) (hm : 0 < m) (hh : 0 < h) (hv : v =  m / h) (ht : t = h / v):
    t = h ^ 2 / m := by
  have h1 : v = m / h := by 
    linarith [hv]
  rw [ht]
  rw [h1]
  field_simp [show 0 < m by linarith, show 0 < h by linarith]
  <;> ring