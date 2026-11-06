import Mathlib

open Real

theorem algebra_279148 {f : ℝ → ℝ}
    (hf : f = fun x => (3 * x - 1) * (sqrt (9 * x ^ 2 - 6 * x + 5) + 1) +
      (2 * x - 3) * (sqrt (4 * x ^ 2 - 12 * x + 13) + 1)) :
    ∃ x, f x = 0 ∧ x = 4 / 5 := by
  use 4 / 5
  constructor
  · -- Show that f(4/5) = 0
    rw [hf]
    have h1 : sqrt (9 * (4 / 5) ^ 2 - 6 * (4 / 5) + 5) = Real.sqrt 149 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : sqrt (4 * (4 / 5) ^ 2 - 12 * (4 / 5) + 13) = Real.sqrt 149 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    simp [h1, h2]
    <;> field_simp <;> ring_nf <;> norm_num
    <;> ring
  · -- Trivial since we use the specific x
    rfl