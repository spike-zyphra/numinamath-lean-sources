import Mathlib

theorem algebra_157978 (x a : ℝ) (hx : x ≠ 1) :
    ∑ i ∈ Finset.range 9, (x^(i + 1) + (i + 1) * a) =
    (x^10 - x) / (x - 1) + 45 * a := by
  have hne : x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  field_simp [hne]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf
  <;> simp [pow_succ, mul_add, add_mul]
  <;> ring