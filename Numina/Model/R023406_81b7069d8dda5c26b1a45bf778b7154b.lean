import Mathlib


theorem inequalities_597039 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (hsum : ∑ i, a i = S) (h : ∀ i, a i ^ 2 / (a i - 1) > S) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by
  have ha0 : 1 < a 0 := ha 0
  have ha1 : 1 < a 1 := ha 1
  have ha2 : 1 < a 2 := ha 2
  have h0 : a 0 ^ 2 / (a 0 - 1) > S := h 0
  have h1 : a 1 ^ 2 / (a 1 - 1) > S := h 1
  have h2 : a 2 ^ 2 / (a 2 - 1) > S := h 2
  have h10 : 0 < a 0 - 1 := by linarith
  have h11 : 0 < a 1 - 1 := by linarith
  have h12 : 0 < a 2 - 1 := by linarith
  have h0' : a 0 ^ 2 > S * (a 0 - 1) := by
    have h0_pos : 0 < a 0 - 1 := by linarith
    apply (lt_div_iff' (by linarith)).mp at h0
    nlinarith
  have h1' : a 1 ^ 2 > S * (a 1 - 1) := by
    have h11_pos : 0 < a 1 - 1 := by linarith
    apply (lt_div_iff' (by linarith)).mp at h1
    nlinarith
  have h2' : a 2 ^ 2 > S * (a 2 - 1) := by
    have h12_pos : 0 < a 2 - 1 := by linarith
    apply (lt_div_iff' (by linarith)).mp at h2
    nlinarith
  have h6 : (a 0 + a 1 + a 2) = S := by
    have : ∑ i : Fin 3, a i = a 0 + a 1 + a 2 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    linarith [hsum, this]
  have pos1 : 0 < a 0 + a 1 := by linarith
  have pos2 : 0 < a 1 + a 2 := by linarith
  have pos3 : 0 < a 2 + a 0 := by linarith
  have h7 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by
    have h8 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 =
        ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) / ((a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0)) := by
      field_simp
      ring
    rw [h8]
    have pos2 : (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by
      nlinarith [mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha1), mul_pos (sub_pos.mpr ha0) (sub_pos.mpr ha2), mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2),
        sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 1 - a 2),
        mul_pos (show 0 < a 0 - 1 by linarith) (show 0 < a 1 - 1 by linarith),
        mul_pos (show 0 < a 0 - 1 by linarith) (show 0 < a 2 - 1 by linarith),
        mul_pos (show 0 < a 1 - 1 by linarith) (show 0 < a 2 - 1 by linarith)]
    have pos3 : (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by positivity
    apply div_pos
    linarith
    all_goals linarith
  linarith