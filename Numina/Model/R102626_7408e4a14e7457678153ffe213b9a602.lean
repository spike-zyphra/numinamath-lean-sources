import Mathlib

theorem algebra_2598 {a : ℝ} (ha : a^3 + 3 * a^2 + 3 * a + 2 = 0) :
    (a + 1)^1996 + (a + 1)^1997 + (a + 1)^1998 = 1 := by
  have h1 : (a + 1) ^ 3 = -1 := by
    nlinarith
  have h2 : a + 1 = -1 := by
    have h3 : (a + 1) ^ 3 + 1 = 0 := by linarith
    have h4 : (a + 1 + 1) * ((a + 1) ^ 2 - (a + 1) + 1) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case $a + 1 + 1 = 0$, which is $a + 2 = 0$ so $a + 1 = -1$ 
      linarith 
    · -- Case $(a + 1)^2 - (a + 1) + 1 = 0$
      have h7 : (a + 1) ^ 2 - (a + 1) + 1 > 0 := by
        nlinarith [sq_nonneg (a + 1 - 1 / 2)]
      nlinarith
  have h4 : (a + 1) ^ 1996 = 1 := by 
    rw [h2]
    norm_num
  have h5 : (a + 1) ^ 1997 = -1 := by 
    rw [h2]
    norm_num
  have h6 : (a + 1) ^ 1998 = 1 := by 
    rw [h2]
    norm_num
  rw [h4, h5, h6]
  norm_num