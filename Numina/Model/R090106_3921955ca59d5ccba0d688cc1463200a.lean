import Mathlib

theorem algebra_270982 (repl : ℕ) (hrepl : repl = 28 - 10) (avg : ℝ)
    (havg : avg = (252 / 28) + 0.5) :
    repl * avg = 171 := by
  have h1 : (repl : ℝ) = (18 : ℝ) := by
    rw [hrepl]
    norm_num
  have h2 : avg = (9.5 : ℝ) := by
    rw [havg]
    norm_num
  rw [h2]
  rw [h1]
  all_goals norm_num