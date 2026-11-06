import Mathlib

theorem algebra_318536 {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : f = fun x => a * x ^ 2 + (1 - 4 * a) * x - 2)
    (h : ∀ x, 0 < x → f x = 8 / x → x = 4) :
    f 4 = 2 := by
  rw [hf]
  all_goals norm_num
  <;> ring_nf <;> norm_num