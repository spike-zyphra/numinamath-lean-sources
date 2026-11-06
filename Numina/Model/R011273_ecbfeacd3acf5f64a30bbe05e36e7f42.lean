import Mathlib
open Real

theorem inequalities_614004 (x : ℝ) (hx : 1 < x) : 1 - 1 / x < log x ∧ log x < x - 1:= by
  have h1 : ∀ x : ℝ, x > 0 → x ≠ 1 → log x < x - 1:= by
    intro x hx hx1
    suffices rexp (log x) < rexp (x - 1) by exact log_lt_sub_one_of_pos hx hx1
    rw [show rexp (log x) = x by exact Real.exp_log hx]
    replace hx1 : x - 1 ≠ 0:= by exact sub_ne_zero_of_ne hx1
    have h1:= Real.add_one_lt_exp hx1
    linarith
  constructor
  · -- the first of the bound.
    suffices h : -log x < 1 / x - 1 from by
      linarith
    have eq1 : -log x = log (1 / x) := by 
      simp [log_div, log_one]
    rw [eq1]
    have hx_pos : 1 / x > 0 := by 
      positivity
    have hx_ne : 1 / x ≠ 1 := by 
      by_contra h_eq
      have h_eq2 : x = 1 := by
        field_simp at h_eq
        <;> nlinarith
      linarith
    have hx_lt1 : 1 / x < 1 := by 
      have h2 : 1 / x < 1 := by
        apply (div_lt_iff' (by linarith)).mpr
        nlinarith
      linarith
    have h8 : log (1 / x) < (1 / x) - 1 := by
      apply h1
      all_goals
      try linarith
    linarith 
  · -- the second of the bound.
    apply h1 
    all_goals 
      try linarith