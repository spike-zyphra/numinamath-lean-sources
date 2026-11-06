import Mathlib

open Real Set

theorem algebra_246067 (f : ℝ → ℝ) (hf : f = fun x => sqrt (2 * x ^ 2 - 2 * x + 1) + sqrt (2 * x ^ 2 - 10 * x + 13)) :
    IsLeast (range f) (sqrt 10) := by
  constructor
  · use 3 / 2
    simp_rw [hf]
    ring_nf
    field_simp
    conv => lhs; rw [← sqrt_sq (show 0 ≤ 2 by norm_num), ← sqrt_mul (by norm_num)]
    conv => rhs; rw [← sqrt_mul (by norm_num)]
    congr 1
    ring
  · rintro y ⟨x, hy⟩
    simp_rw [← hy, hf]
    have h1 : 2 * x ^ 2 - 2 * x + 1 = (x - 1) ^ 2 + (x - 0) ^ 2 := by ring
    have h2 : 2 * x ^ 2 - 10 * x + 13 = (x - 2) ^ 2 + (x - 3) ^ 2 := by ring
    rw [h1, h2]
    convert Lp_add_le (.univ) ![x - 1, x - 0] ![2 - x, 3 - x] one_le_two using 1
    . norm_num [sqrt_eq_rpow]
    . norm_num [sqrt_eq_rpow]
      ring_nf