import Mathlib

open Real

theorem algebra_66756 {x : ℝ} (hx : 0 < x) :
    (log (x ^ 4)) ^ 2 = (log x) ^ 6 ↔ x = 1 ∨ x = exp 2 ∨ x = exp (-2) := by
  constructor
  · -- Assume $(\ln(x^4))^2 = (\ln(x))^6$, prove $x = 1 \lor x = \exp 2 \lor x = \exp(-2)$.
    intro h_eq
    have h1 : log (x ^ 4) = 4 * log x := by
      simp [log_pow]
    rw [h1] at h_eq
    have h2 : 16 * (log x) ^ 2 = (log x) ^ 6 := by
      nlinarith
    have h3 : (log x) ^ 6 - 16 * (log x) ^ 2 = 0 := by
      linarith
    have h4 : (log x) ^ 2 * ((log x) ^ 2 - 4) * ((log x) ^ 2 + 4) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · cases' (mul_eq_zero.mp h5) with h7 h8
      · -- h7: (log x) ^ 2 = 0.
        have hlog0 : log x = 0 := by
          nlinarith
        have hx1 : x = 1 := by
          rw [log_eq_zero] at hlog0
          rcases hlog0 with (r | r | r)
          · linarith
          · linarith
          · linarith
        left
        exact hx1
      · -- h8: (log x) ^ 2 - 4 = 0.
        have hln2_or_neg2 : (log x) ^ 2 = 4 := by
          nlinarith
        have hln2_or_neg2' : log x = 2 ∨ log x = -2 := by
          have h : (log x) ^ 2 = 4 := hln2_or_neg2
          have : log x = 2 ∨ log x = -2 := by
            have h1 : (log x - 2) * (log x + 2) = 0 := by
              nlinarith
            cases' (mul_eq_zero.mp h1) with h2 h3
            · -- h2: (log x) - 2 = 0.
              left
              linarith
            · -- h3: (log x) + 2 = 0.
              right
              linarith
          assumption
        cases hln2_or_neg2' with
        | inl hln2 =>
          have hx2 : x = exp 2 := by
            have : log x = (2 : ℝ) := hln2
            have hx2' : x = Real.exp (log x) := by
              rw [Real.exp_log]
              all_goals linarith
            rw [show log x = (2 : ℝ) by linarith] at hx2'
            linarith
          right
          left
          exact hx2
        | inr hln_neg2 =>
          have hx3 : x = exp (-2) := by
            have : log x = (-2 : ℝ) := hln_neg2
            have hx3' : x = Real.exp (log x) := by
              rw [Real.exp_log]
              all_goals linarith
            rw [show log x = (-2 : ℝ) by linarith] at hx3'
            linarith
          right
          right
          exact hx3
    · -- h6: (log x) ^ 2 + 4 = 0.
      nlinarith [sq_nonneg (log x)]
  · -- Assume x = 1 ∨ x = exp 2 ∨ x = exp (-2), prove (log (x ^ 4)) ^ 2 = (log x) ^ 6.
    rintro (hx | hx | hx)
    · -- hx : x = 1
      rw [hx]
      have h1 : log (1 ^ 4) = 4 * log 1 := by
        simp [log_pow]
      rw [h1]
      have hlog1 : log 1 = 0 := by
        simp
      rw [hlog1]
      all_goals
        norm_num
    · -- hx : x = exp 2
      rw [hx]
      have h2 : log ((exp 2) ^ 4) = 4 * log (exp 2) := by
        simp [log_pow]
      rw [h2]
      have hlogexp2 : log (exp 2) = 2 := by
        simp [log_exp]
      rw [hlogexp2]
      all_goals
        norm_num
    · -- hx : x = exp (-2)
      rw [hx]
      have h3 : log ((exp (-2)) ^ 4) = 4 * log (exp (-2)) := by
        simp [log_pow]
      rw [h3]
      have hlogexp2 : log (exp (-2)) = -2 := by
        simp [log_exp]
      rw [hlogexp2]
      all_goals
        norm_num