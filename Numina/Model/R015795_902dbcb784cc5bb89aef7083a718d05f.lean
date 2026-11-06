import Mathlib

theorem inequalities_242641 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (h : ∑ i, a i = S) (h' : ∀ i, (a i)^2 / (a i - 1) > S) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by
  have h1 : 1 < a 0 := ha 0
  have h2 : 1 < a 1 := ha 1
  have h3 : 1 < a 2 := ha 2
  have hS0 : S = a 0 + a 1 + a 2 := by
    have h_eq : ∑ i : Fin 3, a i = a 0 + a 1 + a 2 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    rw [h_eq] at h
    linarith
  have h40 : (a 0) ^ 2 > S * (a 0 - 1) := by
    have h40 : (a 0)^2 / (a 0 - 1) > S := h' 0
    have h10 : a 0 - 1 > 0 := by linarith
    apply (lt_div_iff₀ (by linarith)).mp at h40
    nlinarith
  have h41 : (a 1) ^ 2 > S * (a 1 - 1) := by
    have h41 : (a 1)^2 / (a 1 - 1) > S := h' 1
    have h11 : a 1 - 1 > 0 := by linarith
    apply (lt_div_iff₀ (by linarith)).mp at h41
    nlinarith
  have h42 : (a 2) ^ 2 > S * (a 2 - 1) := by
    have h42 : (a 2)^2 / (a 2 - 1) > S := h' 2
    have h12 : a 2 - 1 > 0 := by linarith
    apply (lt_div_iff₀ (by linarith)).mp at h42
    nlinarith
  have pair1 : a 0 + a 1 > 0 := by nlinarith
  have pair2 : a 1 + a 2 > 0 := by nlinarith
  have pair3 : a 2 + a 0 > 0 := by nlinarith
  have h6 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by
    have h7 : (1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1) = 
      ((a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) / ((a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) := by
      field_simp [show (a 0 + a 1) ≠ 0 by nlinarith, show (a 1 + a 2) ≠ 0 by nlinarith, show (a 2 + a 0) ≠ 0 by nlinarith]
      ring
    rw [h7] at *
    have h8 : (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by
      rw [show S = a 0 + a 1 + a 2 by linarith] at h40 h41 h42
      nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h1),
        mul_pos (show 0 < a 0 by linarith) (show 0 < a 1 by linarith), mul_pos (show 0 < a 1 by linarith) (show 0 < a 2 by linarith), mul_pos (show 0 < a 2 by linarith) (show 0 < a 0 by linarith)]
    have h9 : (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by positivity
    apply div_pos h8 (by positivity)
  linarith