import Mathlib

theorem algebra_194153 (v : ℝ) (h : v > 0) (t1 t2 : ℝ)
    (ht1 : t1 = 5 / (v + w)) (ht2 : t2 = 5 / (v - w)) (hw : w > 0)
    (h1 : t1 * 2 = t2 * 3) (h2 : t1 + t2 = 10 / v) :
    w = 5 / 12 := by
  rw [ht1] at h1
  rw [ht2] at h1
  rw [ht1] at h2
  rw [ht2] at h2
  field_simp [(show v + w ≠ 0 by nlinarith [h, hw]), (show v - w ≠ 0 by
    by_contra h'
    have : v = w := by linarith
    rw [this] at h1
    field_simp [hw] at h1 ⊢
    <;> nlinarith
  )] at h1 h2 ⊢
  <;> nlinarith [h, hw]