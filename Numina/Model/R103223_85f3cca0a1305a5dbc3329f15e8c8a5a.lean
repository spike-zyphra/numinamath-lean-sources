import Mathlib

theorem algebra_94118 (d t1 t2 : ℝ) (ht1 : t1 = d / 10) (ht2 : t2 = d / 20)
    (hd : d > 0) :
    (2 * d) / (t1 + t2) = 13 + 1 / 3 := by
  have h1 : t1 + t2 = (3 * d) / 20 := by
    rw [ht1, ht2]
    ring
  have h2 : (2 * d) / (t1 + t2) = (2 * d) / ((3 * d) / 20) := by
    rw [h1]
  have h3 : (2 * d) / ((3 * d) / 20) = 40 / 3 := by
    have h4 : d ≠ 0 := by linarith
    field_simp
    <;> ring_nf <;> linarith
  rw [h2, h3]
  <;> norm_num
  <;> linarith