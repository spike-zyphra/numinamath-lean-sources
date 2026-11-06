import Mathlib

theorem algebra_179563 {a d : ℕ} (h₀ : a + d ≠ 0) (h₁ : (a * (a + d) * (a + 2 * d)) = 6)
    (h₂ : (a * (a + d) * (a + 2 * d) * (a + 3 * d)) = 24) :
    a = 1 ∧ d = 1 := by
  have eq2 : a + 3 * d = 4 := by
    have eq3 : a * (a + d) * (a + 2 * d) * (a + 3 * d) = 24 := by
      linarith
    -- Now we need to rewrite the equation as h₁ multiplied by (a + 3d):
    have eq4 : a * (a + d) * (a + 2 * d) * (a + 3 * d) = (a * (a + d) * (a + 2 * d)) * (a + 3 * d) := by
      ring
    rw [eq4] at eq3
    rw [h₁] at eq3
    omega
  have h3 : a ≤ 4 := by 
    omega
  have h4 : d ≤ 1 := by
    omega
  have ha1 : a = 1 := by 
    interval_cases a <;> interval_cases d 
      <;> omega
  have hd1 : d = 1 := by 
    omega
  exact ⟨ha1, hd1⟩