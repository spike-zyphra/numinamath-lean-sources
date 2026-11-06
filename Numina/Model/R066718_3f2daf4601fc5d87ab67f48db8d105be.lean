import Mathlib

theorem algebra_199499 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a + c = 2 * b) (h₂ : b + c = 3 * a) :
    c > a ∧ c > b := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have eq1 : a = 2 * b - c := by linarith
  have eq2 : a = (b + c)/3 := by linarith
  have eq3 : 2 * b - c = (b + c)/3 := by 
    linarith [eq1, eq2]
  have eq4 : 5 * b = 4 * c := by
    linarith [eq3]
  have eq5 : b = 4 * c / 5 := by
    linarith [eq4]
  have eq6 : a = 3 * c / 5 := by
    rw [eq5] at eq1
    linarith
  constructor
  · -- Show c > a
    linarith [eq6, hc]
  · -- Show c > b
    linarith [eq5, hc]