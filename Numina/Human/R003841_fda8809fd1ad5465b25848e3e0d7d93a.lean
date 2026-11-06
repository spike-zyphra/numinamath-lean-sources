import Mathlib

open Real Set

theorem algebra_215519 {b A B C : ℝ}
  (hA : A ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π)
  (hABC : A + B + C = π) (hb1 : b ≠ 1) (hb2 : b > 0)
  (h1 : logb (sqrt b) (C / A) = logb b (4 * (C / A) - 4))
  (h1domain: C / A > 1)
  (h2 : logb (sqrt b) (sin B / sin A) = logb b (4 * (sin B / sin A) - 4))
  (h2domain: sin B / sin A > 1)
  : A ≠ C ∧ B = π / 2 := by

  have : π > 0 := pi_pos

  have h_eq : ∀ x : ℝ, x > 1 → logb (sqrt b) x = logb b (4 * x - 4) → x = 2 := by
    intro x hx h
    rw [← inv_logb] at h
    rw [sqrt_eq_rpow] at h
    rw [logb_rpow_eq_mul_logb_of_pos (by linarith)] at h
    rw [← inv_logb] at h
    field_simp at h
    rw [← logb_rpow_eq_mul_logb_of_pos (by linarith)] at h

    have hx1 : x ^ 2 ∈ Ioi 0 := by
      simp
      positivity
    have hx2 : 4 * x - 4 ∈ Ioi 0 := by
      simp
      linarith

    rcases lt_trichotomy b 1 with (hb3 | rfl | hb4)
    . apply logb_injOn_pos_of_base_lt_one hb2 hb3 at h
      norm_cast at h
      have : (x-2)^2 = 0 := by linarith
      simp at this
      linarith
      all_goals norm_cast


    . norm_num at hb1
    . apply logb_injOn_pos hb4  at h
      norm_cast at h
      have : (x-2)^2 = 0 := by linarith
      simp at this
      linarith
      all_goals norm_cast


  have h_A_ne_zero : A ≠ 0 := by
    have := hA.1
    linarith

  have h_eq1 := h_eq (C / A) h1domain h1
  have h_eq2 := h_eq (sin B / sin A) h2domain h2

  have hAC : C = 2 * A := by
    field_simp at h_eq1
    exact h_eq1

  have h_A_lt_C : A < C := by
    field_simp at h_eq1
    rw [h_eq1]
    suffices A > 0 by linarith
    exact hA.1

  have h_A_ne_C : A ≠ C := by
    linarith

  have hA1 : sin (3 * A) = 2 * sin A := by
    rw [← h_eq2]
    rw [(by linarith : 3 * A = 2 * A + A)]
    rw [← h_eq1]
    have : sin A ≠ 0 := by
      have := sin_pos_of_pos_of_lt_pi hA.1 hA.2
      linarith
    field_simp
    rw [(by linarith : C + A = π - B)]
    rw [sin_pi_sub]


  have hA2 : 3 * sin A - 4 * (sin A) ^ 3 = 2 * sin A := by
    rw [sin_three_mul] at hA1
    exact hA1

  have hA3 : sin A = 1/2 := by
    have : 4 * (sin A) ^ 3 = sin A := by linarith
    have : sin A * (2 * sin A - 1) * (2 * sin A + 1) = 0 := by linarith
    simp at this
    rcases this with (h | h)
    . rcases h with (h | h)
      . rw [sin_eq_zero_iff_of_lt_of_lt (by linarith) (hA.2)] at h
        rw [h] at hA
        simp at hA

      . linarith
    . have := sin_pos_of_pos_of_lt_pi hA.1 hA.2
      linarith

  have hA4 : A ∈ Icc (-(π / 2)) (π / 2) := by
    constructor
    . linarith
    . by_contra h_contra
      simp at h_contra
      have : C > π := by linarith
      have := hC.2
      linarith

  have hA5 : A = π / 6 := by
    rw [← sin_pi_div_six] at hA3
    have : π / 6 ∈ Icc (-(π / 2)) (π / 2) := by
      constructor
      . linarith
      . linarith
    apply injOn_sin hA4 this at hA3
    exact hA3

  have hB1 : B = π / 2 := by
    linarith

  exact ⟨h_A_ne_C, hB1⟩
