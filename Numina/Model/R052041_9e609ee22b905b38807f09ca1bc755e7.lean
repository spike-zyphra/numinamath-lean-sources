import Mathlib

open Real

theorem inequalities_2238 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : c / (a + b) < a / (b + c)) (h2 : a / (b + c) < b / (c + a)) :
    c < a ∧ a < b := by
  have h1' : 0 < a + b := by linarith
  have h2' : 0 < b + c := by linarith
  have h3' : 0 < c + a := by linarith
  -- h1 to cross-multiplied form
  have h1_mul : c * (b + c) < a * (a + b) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h1
    nlinarith
  -- h2 to cross-multiplied form
  have h2_mul : a * (c + a) < b * (b + c) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h2
    nlinarith
  -- Lean can get:  Expanding h1_mul: b c + c^2 < a^2 + a b
  have h5 : c < a := by
    nlinarith [show 0 < a + b + c by positivity]
  -- similarly
  have h6 : a < b := by
    nlinarith [show 0 < a + b + c by positivity]
  exact ⟨h5, h6⟩