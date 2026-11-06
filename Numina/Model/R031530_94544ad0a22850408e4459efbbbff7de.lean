import Mathlib

theorem algebra_218548 (f : ℝ → ℝ) (hf : ∀ x > 0, f x + 2 * f (1 / x) = 3 * x + 6) :
    ∀ x > 0, f x = 2 / x - x + 2 := by
  intro x hx
  have eq1' : f x + 2 * f (1 / x) = 3 * x + 6 := by 
    specialize hf x hx
    simpa using hf
  have eq2' : f (1 / x) + 2 * f x = 3 * (1 / x) + 6 := by
    have eq2 := hf (1 / x) (by positivity)
    have h1 : 1 / (1 / x) = x := by
      field_simp
    rw [h1] at eq2
    linarith
  have eq3 : 3 * f x = 6 / x - 3 * x + 6 := by
    have eq1 := eq1'
    have eq2 := eq2'
    field_simp at eq1 eq2 ⊢
    nlinarith
  have eq4 : f x = 2 / x - x + 2 := by
    have eq3' : 3 * f x = 6 / x - 3 * x + 6 := eq3
    have eq5 : f x = (6 / x - 3 * x + 6) / 3 := by
      linarith
    rw [eq5]
    field_simp
    <;> ring
  exact_mod_cast eq4