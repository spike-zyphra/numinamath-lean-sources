import Mathlib

open Real

theorem algebra_20591 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (f : ℕ → ℕ → ℝ) (h : ∀ a b, a > 0 → b > 0 → f a b = √(a * b + a) / √(a * b - b)) :
    f 9 2 = 3 * sqrt 3 / 4 := by
  have h92 : f 9 2 = √(9 * 2 + 9) / √(9 * 2 - 2) := by
    apply h 9 2
    all_goals norm_num
  rw [h92]
  have h1 : (9 * 2 + 9 : ℝ) = (27 : ℝ) := by norm_num
  have h2 : (9 * 2 - 2 : ℝ) = (16 : ℝ) := by norm_num
  rw [h1]
  rw [h2]
  have h3 : √(27 : ℝ) = 3 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : √(16 : ℝ) = (4 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3, h4]
  all_goals norm_num