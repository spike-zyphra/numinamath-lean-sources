import Mathlib

theorem algebra_15552 {n : ℕ} (hn : 9^n * 9^n * 9^n * 9^n = 81^4) : n = 2 := by
  have h1 : 9^n * 9^n * 9^n * 9^n = 9^(4 * n) := by
    ring_nf
    <;> simp [pow_mul]
    <;> ring_nf
    <;> omega
  have h2 : (81 : ℕ) ^ 4 = 9 ^ 8 := by
    norm_num
  rw [h1] at hn
  rw [h2] at hn
  have h3 : 4 * n = 8 := by
    exact Nat.pow_right_injective (by norm_num) hn
  have h4 : n = 2 := by
    omega
  exact h4