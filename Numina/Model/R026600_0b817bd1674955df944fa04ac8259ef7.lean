import Mathlib

theorem algebra_323402 (a : ℝ) (h : Complex.abs ((a + 2 * Complex.I) * (1 + Complex.I)) = 4) :
    a = 2 ∨ a = -2 := by
  have h1 : (a + 2 * Complex.I) * (1 + Complex.I) = (a - 2) + (a + 2) * Complex.I := by
    simp [Complex.ext_iff, Complex.I_mul_I, mul_add, add_mul]
    <;> ring_nf <;> norm_num [Complex.I_sq]

  rw [h1] at h

  have h2 : Complex.abs ((a - 2) + (a + 2) * Complex.I) = Real.sqrt ((a - 2) ^ 2 + (a + 2) ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf

  rw [h2] at h

  have h3 : (a - 2) ^ 2 + (a + 2) ^ 2 = 16 := by
    calc
      (a - 2) ^ 2 + (a + 2) ^ 2 = (Real.sqrt ((a - 2) ^ 2 + (a + 2) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 4 ^ 2 := by rw [h]
      _ = 16 := by norm_num

  have h4 : 2 * a ^ 2 + 8 = 16 := by
    nlinarith

  have h5 : a ^ 2 = 4 := by
    nlinarith

  have h6 : a = 2 ∨ a = -2 := by
    have h7 : a ^ 2 - 4 = 0 := by 
      linarith [h5]

    have h8 : (a - 2) * (a + 2) = 0 := by
      linarith [h7]

    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- a - 2 = 0
      left
      linarith
    · -- a + 2 = 0
      right 
      linarith
  exact h6