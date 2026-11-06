import Mathlib

theorem algebra_185593 {a : ℕ → ℝ} (ha : a 2 = 3) (ha' : a 3 = 6)
    (ha'' : ∀ n, a (n + 2) = a (n + 1) - 1 / a n) :
    a 5 = 11 / 2 := by
  -- Calculate a4 using n = 2
  have a4 : a 4 = 17 / 3 := by
    specialize ha'' 2
    norm_num [ha, ha'] at ha''
    linarith
  -- Calculate a5 using n = 3 and the value of a4
  specialize ha'' 3
  norm_num [ha', a4] at ha''
  linarith [ha'']