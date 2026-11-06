import Mathlib

theorem algebra_12011 {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (f : ℝ → ℝ) (hf : ∀ x, x > 0 → f x = a * x + 3)
    (hf' : f 0 = a * b) (hf'' : ∀ x, x < 0 → f x = b * x + c) (h2 : f 2 = 5)
    (h0 : f 0 = 5) (h1 : f (-2) = -10) : a + b + c = 6 := by
  have h_eq1 : f 2 = (a : ℝ) * (2 : ℝ) + 3 := by 
    specialize hf 2 (by norm_num)
    simpa using hf
  have eq_a1 : (a : ℝ) = 1 := by
    nlinarith
  have eq_a1' : a = 1 := by
    exact_mod_cast eq_a1
  have eq4 : (f 0) = (a * b : ℝ) := by
    simpa using hf'
  have eq4' : (a * b : ℝ) = 5 := by
    nlinarith
  have eq4'' : a * b = 5 := by
    exact_mod_cast eq4'
  have eq_b : b = 5 := by
    rw [eq_a1'] at eq4''
    linarith
  -- Now using f(-2) = -10
  have h_eq3 : f (-2 : ℝ) = (b : ℝ) * (-2 : ℝ) + (c : ℝ) := by
    specialize hf'' (-2) (by norm_num)
    simpa using hf''
  have eq3' : (b : ℝ) * (-2 : ℝ) + (c : ℝ) = -10 := by
    nlinarith
  have eq3'' : b * (-2) + c = -10 := by
    exact_mod_cast eq3'
  have eq_c : c = 0 := by 
    rw [eq_b] at eq3''
    linarith
  omega