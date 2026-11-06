import Mathlib

theorem inequalities_50245 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (S : ℝ) (hS : S = ∑ i, a i) (h : ∀ i, a i ^ 2 / (a i - 1) > S) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by

  have ha1 : 1 < a 0 := ha 0
  have ha2 : 1 < a 1 := ha 1
  have ha3 : 1 < a 2 := ha 2

  have hS0 : S = a 0 + a 1 + a 2 := by
    rw [hS]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring

  have h1 : a 0 ^ 2 / (a 0 - 1) > S := h 0
  have h2 : a 1 ^ 2 / (a 1 - 1) > S := h 1
  have h3 : a 2 ^ 2 / (a 2 - 1) > S := h 2

  have h11 : a 0 - 1 > 0 := by linarith
  have h12 : a 1 - 1 > 0 := by linarith
  have h13 : a 2 - 1 > 0 := by linarith

  have h21 : a 0 ^ 2 > (a 0 - 1) * S := by
    have : a 0 ^ 2 / (a 0 - 1) > S := h1
    apply (lt_div_iff₀ (by linarith)).mp at this
    linarith

  have h41 : a 1 ^ 2 > (a 1 - 1) * S := by
    have : a 1 ^ 2 / (a 1 - 1) > S := h2
    apply (lt_div_iff₀ (by linarith)).mp at this
    linarith

  have h31 : a 2 ^ 2 > (a 2 - 1) * S := by
    have : a 2 ^ 2 / (a 2 - 1) > S := h3
    apply (lt_div_iff₀ (by linarith)).mp at this
    linarith

  rw [hS0] at h21 h41 h31

  have pos1 : 0 < a 0 + a 1 := by
    linarith [ha1, ha2]

  have pos2 : 0 < a 1 + a 2 := by
    linarith [ha2, ha3]

  have pos3 : 0 < a 2 + a 0 := by
    linarith [ha3, ha1]

  have h5 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by
    have pos12 : 0 < (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) := by
      positivity
    have h5' : ( 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 ) = ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) := by 
      field_simp
      <;> ring
    rw [h5']
    have h6 : ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) > 0 := by
      nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2), 
                  mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha3), 
                  mul_pos (sub_pos.mpr ha3) (sub_pos.mpr ha1),
                  h21, h41, h31
                 ]
    have h7 : ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) > 0 := by
      positivity
    apply div_pos
    · linarith [h6]
    · linarith [h7]

  linarith