import Mathlib

theorem algebra_4918 {x : ℂ} (hx : x ≠ 0) (h : x + 1 / x = 21) :
  x ^ 2 + 1 / x ^ 2 = 439 := by
  have eq1 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
    field_simp [hx]
    ring
  rw [eq1, h]
  norm_num
  <;> try simp [Complex.ext_iff] <;> norm_num