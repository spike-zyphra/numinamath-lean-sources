import Mathlib

theorem algebra_286793 {a : ℝ} (ha : a = (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1)) :
    a^4 - 5 * a^3 + 10 * a^2 - 11 * a + 4 = 1 := by

  have ha2 : a = (3 - Real.sqrt 5) / 2 := by
    rw [ha]
    have h2 : Real.sqrt 5 + 1 ≠ 0 := by
      positivity
    field_simp [h2, sub_ne_zero.mpr h2]
    <;> ring_nf <;> norm_num
    <;> ring

  have h_eq : a^2 - 3 * a + 1 = 0 := by
    rw [ha2]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]

  have h_a2 : a^2 = 3 * a - 1 := by
    linarith

  have h_a3 : a^3 = 8 * a - 3 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (3 * a - 1) := by rw [h_a2]
      _ = 3 * a^2 - a := by ring
      _ = 3 * (3 * a - 1) - a := by rw [h_a2]
      _ = 8 * a - 3 := by ring

  have h_a4 : a^4 = 21 * a - 8 := by
    calc
      a^4 = (a^2)^2 := by ring
      _ = (3 * a - 1)^2 := by rw [h_a2]
      _ = 9 * a^2 - 6 * a + 1 := by ring
      _ = 9 * (3 * a - 1) - 6 * a + 1 := by rw [h_a2]
      _ = 21 * a - 8 := by ring

  calc
    a^4 - 5 * a^3 + 10 * a^2 - 11 * a + 4
        = (21 * a - 8) - 5 * (8 * a - 3) + 10 * (3 * a - 1) - 11 * a + 4 := by
          rw [h_a4, h_a3, h_a2]
    _ = 0 * a + 1 := by
      linarith
    _ = 1 := by
      linarith