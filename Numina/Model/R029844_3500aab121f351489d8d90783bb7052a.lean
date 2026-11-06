import Mathlib

open Real

theorem algebra_183913 {a b c t : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (ht : 1 < t) (h : 2 / logb b t = 1 / logb a t + 1 / logb c t) :
    2 * b ≤ a + c := by
  have h1 : logb b t = log t / log b := by
    field_simp [logb]

  have h2 : logb a t = log t / log a := by
    field_simp [logb]

  have h3 : logb c t = log t / log c := by
    field_simp [logb]

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h

  have ht' : log t > 0 := by
    apply log_pos
    linarith

  have h4 : 2 * log b = log a + log c := by
    field_simp [ht'] at h
    linarith

  have h5 : log (b ^ 2) = log (a * c) := by
    have h6 : log (b ^ 2) = 2 * log b := by
      simp [log_pow]
    have h7 : log (a * c) = log a + log c := by
      rw [log_mul (by linarith [ha.1]) (by linarith [hc.1])]
    linarith [h4, h6, h7]

  have h6 : b ^ 2 = a * c := by
    have pos1 : 0 < b ^ 2 := by nlinarith [hb.1]
    have pos2 : 0 < a * c := by nlinarith [ha.1, hc.1]
    have h7 : log (b ^ 2) = log (a * c) := h5
    have h8 : b ^ 2 = a * c := by
      exact log_injOn_pos (Set.mem_Ioi.mpr pos1) (Set.mem_Ioi.mpr pos2) h7
    linarith

  nlinarith [sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (b - c), h6, mul_pos ha.1 hb.1, mul_pos ha.1 hc.1, mul_pos hb.1 hc.1]