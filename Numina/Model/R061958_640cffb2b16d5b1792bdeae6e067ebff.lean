import Mathlib

theorem algebra_20620 (a : ℕ) (ha : 0 < a) (h : Real.sqrt a + Real.sqrt 9 = 5) :
    a = 4 := by
  have h1 : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_cases]
    norm_num
  rw [h1] at h
  have h2 : Real.sqrt (a : ℝ) = 2 := by
    linarith
  have h3 : (a : ℝ) = 4 := by
    calc
      (a : ℝ) = (Real.sqrt (a : ℝ)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 2 ^ 2 := by rw [h2]
      _ = (4 : ℝ) := by norm_num
  have ha4 : a = 4 := by
    exact_mod_cast h3
  exact ha4