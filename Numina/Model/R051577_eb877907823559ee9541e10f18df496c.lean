import Mathlib

theorem algebra_281756 {x y : ℝ} (h₀ : 15 * x + 12 * y = 1000 + 710) (h₁ : x = y - 30) :
    x = 50 ∧ y = 80 := by 
  have eq1 : y = 80 := by
    rw [h₁] at h₀ -- substituting x with y - 30 in the first equation
    linarith -- solving the linear arithmetic
  have eq2 : x = 50 := by 
    rw [eq1] at h₁ -- substituting y = 80 into the equation x = y - 30
    linarith -- computing the value of x
  exact ⟨eq2, eq1⟩ -- proving the final goal with conjunction