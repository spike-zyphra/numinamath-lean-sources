import Mathlib

theorem algebra_207528 {x y : ℕ} (hx : x + y ≠ 0) (hy : y ≠ 0)
    (hxy : x = (y / (x + y : ℝ)) * 100 ∧ y = (x / (x + y : ℝ)) * 100) :
    x = 50 ∧ y = 50 := by
  rcases hxy with ⟨hx_eq, hy_eq⟩
  have h1 : (x : ℝ) + (y : ℝ) ≠ 0 := by
    have h2 : (x : ℝ) + (y : ℝ) = (x + y : ℝ) := by ring
    rw [h2] 
    exact_mod_cast hx
  have eq1 : (x : ℝ) = ((y / ((x + y : ℝ))) * 100) := by
    simpa using hx_eq
  have eq2 : (y : ℝ) = ((x / ((x + y : ℝ))) * 100) := by
    simpa using hy_eq
  have h2 : (x : ℝ) * ((x + y : ℝ)) = (y : ℝ) * 100 := by
    have h3 : (x + y : ℝ) ≠ 0 := h1
    field_simp at eq1
    nlinarith [eq1]
  have h3 : (y : ℝ) * ((x + y : ℝ)) = (x : ℝ) * 100 := by
    have h4 : (x + y : ℝ) ≠ 0 := h1
    field_simp at eq2
    nlinarith [eq2]
  have h4 : ((x + y : ℝ)) ^ 2 = (x + y : ℝ) * 100 := by
    nlinarith [h2, h3]
  have h5 : (x : ℝ) + (y : ℝ) = 100 := by
    have h6 : (x + y : ℝ) ≠ 0 := h1
    have h7 : (x + y : ℝ) = 100 := by
      apply (mul_left_inj' h6).mp
      linarith 
    linarith
  have h7 : (x : ℝ) = (y : ℝ) := by
    nlinarith [h2, h5]
  have h6 : (x : ℝ) + (y : ℝ) = 100 := h5
  have h8 : (x : ℝ) = 50 := by 
    nlinarith [h7, h5]
  have h9 : (y : ℝ) = 50 := by
    nlinarith [h7, h5]
  constructor
  · -- x = 50
    have h10 : x = 50 := by 
      exact_mod_cast (show (x : ℝ) = (50 : ℝ) by linarith)
    exact h10
  · -- y = 50
    have h11 : y = 50 := by 
      exact_mod_cast (show (y : ℝ) = (50 : ℝ) by linarith)
    exact h11