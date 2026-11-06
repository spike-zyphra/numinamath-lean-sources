import Mathlib

open Real

theorem algebra_231779 {f r : ℝ} (hf : 0 < f) (hr : ∃ q : ℚ, r = q) :
    log (f ^ r) = r * log f := by
  rcases hr with ⟨q, hrq⟩
  rw [hrq]
  have h : log (f ^ (q : ℝ)) = (q : ℝ) * log f := by
    rw [log_rpow]
    all_goals
      try exact_mod_cast hf
      all_goals
        try linarith [hf]
  simpa using h