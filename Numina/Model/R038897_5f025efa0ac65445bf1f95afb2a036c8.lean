import Mathlib

open Real

theorem algebra_8294 {f : ℝ → ℝ} (hf : f = λ x => abs (log x)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (h : a < b) (h1 : f a = f b) :
    2024 * a + 2025 * b ≥ 4049 := by
  have h2 : abs (log a) = abs (log b) := by
    rw [hf] at h1 
    simpa using h1

  cases abs_eq_abs.1 h2 with
  | inl h3 =>
    have h3' : log a = log b := h3
    have h3a : a = b := by
      apply log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) h3'
    linarith
  | inr h4 =>
    have h4' : log a = -log b := h4
    have h5 : a * b = 1 := by
      have h6 : log (a * b) = 0 := by
        have h7 : log (a * b) = log a + log b := by
          rw [log_mul (by linarith) (by linarith)]
        rw [h7]
        linarith [h4']
      have h8 : a * b = 1 := by
        have h9 : a * b > 0 := by
          nlinarith
        have h10 : a * b = (Real.exp (log (a * b))) := by
          rw [Real.exp_log]
          all_goals nlinarith
        rw [h10, h6]
        norm_num
      linarith
    have h6 : 2024 * a + 2025 * b ≥ 4049 := by
      nlinarith [sq_nonneg (a - 1 / a), sq_nonneg (b - a), sq_nonneg (a - 45 / 44), sq_nonneg (b - 44 / 45), 
        mul_pos ha hb, h5, mul_pos (show 0 < b - a by linarith) (show 0 < b by linarith)]
    linarith