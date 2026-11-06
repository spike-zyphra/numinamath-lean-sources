import Mathlib

theorem algebra_14597 (a b x : ℕ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (h : Real.sqrt a + Real.sqrt b = x) (h1 : a = 36) (h2 : b = 25) :
    x = 11 := by
  have h3 : (a : ℝ) = (36 : ℝ) := by exact_mod_cast h1
  have h4 : (b : ℝ) = (25 : ℝ) := by exact_mod_cast h2
  have h5 : Real.sqrt (a : ℝ) = (6 : ℝ) := by 
    rw [h3]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h6 : Real.sqrt (b : ℝ) = (5 : ℝ) := by
    rw [h4]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h7 : (Real.sqrt (a : ℝ) + Real.sqrt (b : ℝ) : ℝ) = (x : ℝ) := by
    exact_mod_cast h
  rw [h5, h6] at h7
  have h8 : (x : ℝ) = (11 : ℝ) := by
    nlinarith
  have h9 : x = 11 := by 
    exact_mod_cast h8
  exact h9