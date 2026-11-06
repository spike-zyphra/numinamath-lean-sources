import Mathlib

open Real

theorem inequalities_311109 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (S : ℝ) (hS : S = ∑ i, a i) (h : ∀ i, a i ^ 2 / (a i - 1) > S) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by

  have h1 : 1 < a 0 := ha 0
  have h2 : 1 < a 1 := ha 1
  have h3 : 1 < a 2 := ha 2

  have hS0 : S = a 0 + a 1 + a 2 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hS]

  have h00 : a 0 ^ 2 > S * (a 0 - 1) := by
    have h10 : 0 < a 0 - 1 := by linarith
    have h0' : a 0 ^ 2 / (a 0 - 1) > S := h 0
    apply (lt_div_iff₀ (by linarith)).mp at h0'
    nlinarith

  have h11 : a 1 ^ 2 > S * (a 1 - 1) := by
    have h10 : 0 < a 1 - 1 := by linarith
    have h11' : a 1 ^ 2 / (a 1 - 1) > S := h 1
    apply (lt_div_iff₀ (by linarith)).mp at h11'
    nlinarith

  have h22 : a 2 ^ 2 > S * (a 2 - 1) := by
    have h20 : 0 < a 2 - 1 := by linarith
    have h22' : a 2 ^ 2 / (a 2 - 1) > S := h 2
    apply (lt_div_iff₀ (by linarith)).mp at h22'
    nlinarith

  rw [hS0] at h00 h11 h22

  have h4 : 0 < (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) := by
    positivity

  have h5 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by

    have h6 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 =
      ((a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) / ((a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) := by 
      field_simp
      ring
    rw [h6]

    have h7 : (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by
      nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
        mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
        mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), 
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3)
      ]
    apply div_pos 
    linarith 
    all_goals 
      positivity

  linarith