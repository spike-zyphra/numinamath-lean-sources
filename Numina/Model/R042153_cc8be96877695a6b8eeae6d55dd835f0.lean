import Mathlib

theorem inequalities_194973 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (S : ℝ) (hS : S = ∑ i, a i) (h : ∀ i, (a i)^2 / (a i - 1) > S) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by

  have h1 := h 0
  have h2 := h 1
  have h3 := h 2

  have hS0 : S = a 0 + a 1 + a 2 := by
    simp [hS, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring
  have ha0 : 1 < a 0 := ha 0
  have ha1 : 1 < a 1 := ha 1
  have ha2 : 1 < a 2 := ha 2
  have h4 : a 0 - 1 > 0 := by linarith
  have h5 : a 1 - 1 > 0 := by linarith
  have h6 : a 2 - 1 > 0 := by linarith

  have h7 : (a 0) ^ 2 / (a 0 - 1) > S := h1
  have h8 : (a 1) ^ 2 / (a 1 - 1) > S := h2
  have h9 : (a 2) ^ 2 / (a 2 - 1) > S := h3

  have h7' : (a 0) ^ 2 > S * (a 0 - 1) := by 
    have pos1 : a 0 - 1 > 0 := h4
    apply (lt_div_iff₀ pos1).mp at h7
    linarith
  have h8' : (a 1) ^ 2 > S * (a 1 - 1) := by
    have pos1 : a 1 - 1 > 0 := h5
    apply (lt_div_iff₀ pos1).mp at h8
    linarith
  have h9' : (a 2) ^ 2 > S * (a 2 - 1) := by
    have pos1 : a 2 - 1 > 0 := h6
    apply (lt_div_iff₀ pos1).mp at h9
    linarith

  simp [hS0] at h7' h8' h9' 
  have h10 : 0 < a 0 + a 1 := by linarith
  have h11 : 0 < a 1 + a 2 := by linarith
  have h12 : 0 < a 2 + a 0 := by linarith
  have h13 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by
    have h10 : 0 < a 0 + a 1 := by linarith
    have h11 : 0 < a 1 + a 2 := by linarith
    have h12 : 0 < a 2 + a 0 := by linarith
    have h14 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 =
        ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) := by 
      field_simp
      <;> ring
    rw [h14]
    apply div_pos 
    nlinarith [mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha1), mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2),
              mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha0), 
              mul_pos (show 0 < a 0 + a 1 by linarith) (show 0 < a 1 + a 2 by linarith), 
              mul_pos (show 0 < a 1 + a 2 by linarith) (show 0 < a 2 + a 0 by linarith), 
              mul_pos (show 0 < a 0 + a 1 by linarith) (show 0 < a 2 + a 0 by linarith)
            ]
    positivity
  linarith