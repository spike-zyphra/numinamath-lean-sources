import Mathlib

theorem algebra_378912
    (a : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (h : ∀ n, a (n + 1) = 2 * a n)
    (h1 : a 3 * a 11 = 16) : Real.logb 2 (a 10) = 5 := by

  have h_da (n d : ℕ) : a (n + d) = 2 ^ d * a n := by
    induction d with
    | zero =>
      simp only [add_zero, pow_zero, one_mul]
    | succ d ih =>
      rw [← add_assoc, h, ih]
      ring

  have h_sq_a7 : a 7 ^ 2 = 16 := by
    have t1 : a 3 = a 7 / 2 ^ 4 := by
      rw [h_da 3 4, mul_div_cancel_left₀ (a 3) (by positivity)]
    have t2 : a 11 = 2 ^ 4 * a 7 := by rw [← h_da]
    rw [← h1, t1, t2]
    ring

  have h_a7 : a 7 = 4 := by
    have h_a7_pos : 0 < a 7 := ha 7
    nlinarith only [h_sq_a7, h_a7_pos]

  have h_a10 : a 10 = 2 ^ 5 := by
    norm_num [h_da 7 3, h_a7]

  rw [h_a10, Real.logb_pow]
  norm_num

