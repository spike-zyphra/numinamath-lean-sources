import Mathlib

theorem algebra_6424 {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ x, x * f x + f (-x) = 1) :
    ∀ x, f x = (x + 1) / (x ^ 2 + 1) := by
  intro x
  have eq1 := h x
  have eq2 := h (-x)
  simp at eq2
  have eq3 : f (-x) = 1 - x * f x := by 
    linarith
  rw [eq3] at eq2
  have eq4 : f x * (x ^ 2 + 1) = x + 1 := by
    nlinarith
  have hx2 : x ^ 2 + 1 > (0 : ℝ) := by
    nlinarith [sq_nonneg x]
  have eq5 : f x = (x + 1) / (x ^ 2 + 1) := by
    field_simp [hx2]
    <;> linarith
  exact eq5