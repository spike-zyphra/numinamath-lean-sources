import Mathlib

theorem algebra_15198 (a b : ℝ) (ha : a^2 = 18) (hb : b^2 = 2) :
    2 * √(a^2 + b^2) = 4 * √5 := by
  have h1 : a^2 + b^2 = 20 := by
    rw [ha, hb]
    norm_num
  have h2 : √(a^2 + b^2) = √20 := by
    rw [h1]
  have h3 : √(20 : ℝ) = 2 * √5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : √(a^2 + b^2) = 2 * √5 := by
    rw [h2]
    exact h3
  calc
    2 * √(a^2 + b^2) = 2 * (2 * √5) := by rw [h4]
    _ = 4 * √5 := by ring