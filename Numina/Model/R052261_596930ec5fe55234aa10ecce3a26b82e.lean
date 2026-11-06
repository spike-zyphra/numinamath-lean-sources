import Mathlib

open Real

theorem algebra_307301 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : ∃ d, log x = log y - d ∧ log y = log z - d) :
    y^2 = x * z := by
  rcases h with ⟨d, h₁, h₂⟩
  have h3 : log x + log z = 2 * log y := by
    have eq1 : log x = log y - d := h₁
    have eq2 : log z = log y + d := by
      linarith [h₂]
    linarith [eq1, eq2]
  have h4 : log (x * z) = log x + log z := by
    rw [log_mul (by linarith) (by linarith)]
  have h5 : log (y ^ 2) = 2 * log y := by
    simp [log_pow]
  have h6 : log (x * z) = log (y ^ 2) := by
    linarith [h4, h3, h5]
  have h7 : x * z = y ^ 2 := by
    exact log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (x * z) > (0 : ℝ)))
      (Set.mem_Ioi.mpr (by positivity : (y ^ 2) > (0 : ℝ))) h6
  linarith [h7]