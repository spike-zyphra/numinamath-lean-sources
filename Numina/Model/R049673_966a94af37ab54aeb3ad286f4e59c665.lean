import Mathlib

open Real

theorem algebra_193729 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : ∃ d, log x + d = log y ∧ log y + d = log z) :
    y^2 = x * z := by 
  rcases h with ⟨d, h1, h2⟩
  have eq1 : log y = log x + d := by linarith
  have eq2 : log z = log y + d := by linarith
  have h4 : 2 * log y = log x + log z := by
    linarith [eq1, eq2]
  have h5 : log (y^2) = log (x * z) := by 
    have h6 : log (y^2) = 2 * log y := by 
      simp [log_pow]
    have h7 : log (x * z) = log x + log z := by 
      rw [log_mul (by positivity) (by positivity)]
    rw [h6, h7]
    linarith [h4]
  have h8 : y^2 = x * z := by 
    exact log_injOn_pos (Set.mem_Ioi.mpr (show 0 < y^2 by positivity)) (Set.mem_Ioi.mpr (show 0 < x * z by positivity)) h5
  exact h8