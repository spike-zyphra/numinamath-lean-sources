import Mathlib

theorem algebra_176837 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : (d - 2 * v * 30 / 60) / (v * (1 - 1 / 3)) = 1.5) (h₃ : (d - 2 * v * 50 / 60) / (v * (1 - 1 / 3)) = 1.25) :
    d = 196 ∧ v = 60 := by

  have eq3 : v * (1 - 1 / 3 : ℝ) = (2 / 3) * v := by
    ring_nf

  -- First equation
  have eq4 : (d - 2 * v * 30 / 60) / (v * (1 - 1 / 3 : ℝ)) = 1.5 := h₂

  -- Second equation
  have eq5 : (d - 2 * v * 50 / 60) / (v * (1 - 1 / 3 : ℝ)) = 1.25 := h₃

  -- Manipulate first equation to solve for d
  rw [eq3] at eq4
  field_simp [(show (2 / 3) * v ≠ 0 by nlinarith)] at eq4
  ring_nf at eq4 ⊢

  -- Manipulate second equation to solve for d
  rw [eq3] at eq5
  field_simp [(show (2 / 3) * v ≠ 0 by nlinarith)] at eq5
  ring_nf at eq5 ⊢

  -- Solving the equations
  have h_v : v = 60 := by
    nlinarith
  
  have h_d : d = 196 := by 
    nlinarith [h_v, eq4]

  exact ⟨h_d, h_v⟩