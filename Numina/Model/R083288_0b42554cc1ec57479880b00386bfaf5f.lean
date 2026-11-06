import Mathlib

theorem algebra_471 {c d e f : ℝ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hcd : c / 100 * d / 100 ≠ 0) (hef : e / 100 * f / 100 ≠ 0) :
    (d / 100 * e / 100) / (c / 100 * f / 100) = d * e / (c * f) := by
  field_simp
  <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num
  <;> ring