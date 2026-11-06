import Mathlib

theorem algebra_283714 {a b c : ℝ × ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ¬ Collinear ℝ {a, b, c}) :
    (a • b) • c = a • (b • c) := by
  simp [Finset.sum]
  <;> ring_nf
  <;> aesop