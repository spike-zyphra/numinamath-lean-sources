import Mathlib

theorem number_theory_56783 (N : ℕ) (b : ℕ) (hb : b > 1) (hN : Nat.digits b N = [3, 0, 5])
    (hN' : Nat.digits (b + 2) N = [5, 0, 3]) :
    (Nat.digits 10 N).prod = 64 := by
  have h1 : N = 5 * b ^ 2 + 3 := by
    rw [← Nat.ofDigits_digits b N]
    rw [hN]
    simp [Nat.ofDigits, mul_add, add_mul]
    <;> ring
  have h2 : N = 3 * (b + 2) ^ 2 + 5 := by
    rw [← Nat.ofDigits_digits (b + 2) N]
    rw [hN']
    simp [Nat.ofDigits, mul_add, add_mul]
    <;> ring
  have eq1 : 5 * b ^ 2 + 3 = 3 * (b + 2) ^ 2 + 5 := by
    linarith [h1, h2]
  have eq2 : b = 7 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg ((b + 2 : ℕ)), sq_pos_of_pos (show 0 < (b : ℕ) by linarith), sq_pos_of_pos (show 0 < (b + 2 : ℕ) by nlinarith)]
  have eq3 : N = 248 := by
    rw [eq2] at h1
    nlinarith
  rw [eq3]
  norm_num