import Mathlib

theorem algebra_187635 {a b c d : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x^3 + b * x^2 + c * x + d)
    (h0 : f 0 = 10) (h1 : f 1 = 12) (h2 : f 2 = 4) (h3 : f 3 = 1) :
    a = 5 / 2 ∧ b = -25 / 2 ∧ c = 12 ∧ d = 10 := by
-- Convert the function conditions into equations.
  have h0' : d = 10 := by 
    rw [hf] at h0
    simp at h0 
    linarith
  -- Substituting f(1) = 12 using d = 10.
  have h1' : a + b + c = 2 := by
    rw [hf] at h1
    simp at h1 
    linarith [h0']
  -- Substituting f(2) = 4 using d = 10.
  have h2' : 4 * a + 2 * b + c = -3 := by
    rw [hf] at h2
    simp at h2 
    linarith [h0']
  -- Substituting f(3) = 1 using d = 10.
  have h3' : 9 * a + 3 * b + c = -3 := by
    rw [hf] at h3
    simp at h3 
    linarith [h0']
  -- Solving the resulting system of equations.
  have eq1 : b = -5 - 3 * a := by
    linarith [h1', h2']
  have eq2 : a = 5 / 2 := by
    linarith [h2', h3', eq1]
  have eq3 : b = -25 / 2 := by
    rw [eq2] at eq1
    linarith
  have eq4 : c = 12 := by
    linarith [h1', eq2, eq3]
  exact ⟨eq2, eq3, eq4, h0'⟩