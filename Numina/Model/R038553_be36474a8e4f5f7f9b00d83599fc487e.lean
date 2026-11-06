import Mathlib

theorem algebra_41335 (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2) (h : Real.sin x / (1 + Real.cos x) = 1 / 3) :
    Real.sin (2 * x) / (1 + Real.cos (2 * x)) = 3 / 4 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < Real.pi / 2 := hx.2
  have h1 : 1 + Real.cos x > 0 := by
    have hcos : Real.cos x > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos, hx1, hx2]
    linarith
  have h2 : 3 * Real.sin x = 1 + Real.cos x := by
    field_simp [show 1 + Real.cos x ≠ 0 by linarith] at h
    linarith
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h4 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    . linarith
    . linarith [Real.pi_pos, hx2]
  have h5 : Real.sin x = 3 / 5 := by
    have h6 : Real.cos x = 3 * Real.sin x - 1 := by
      linarith [h2]
    rw [h6] at h3
    have h8 : 10 * Real.sin x ^ 2 - 6 * Real.sin x = 0 := by
      nlinarith
    have h9 : 2 * Real.sin x * (5 * Real.sin x - 3) = 0 := by
      linarith [h8]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- $2 * \sin x = 0$, so $\sin x = 0$, which contradicts $\sin x > 0$.
      have h12 : Real.sin x = 0 := by linarith
      linarith [h4, h12]
    · -- $\sin x = 3/5$
      linarith
  have h12 : Real.cos x = 4 / 5 := by
    have h6 : Real.cos x = 3 * Real.sin x - 1 := by
      linarith [h2]
    rw [h5] at h6
    linarith
  have h13 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have h14 : Real.sin (2 * x) = 24 / 25 := by
    rw [h13, h5, h12]
    norm_num
  have h15 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h16 : Real.cos (2 * x) = 7 / 25 := by
    rw [h15, h12]
    norm_num
  rw [h14, h16]
  all_goals norm_num