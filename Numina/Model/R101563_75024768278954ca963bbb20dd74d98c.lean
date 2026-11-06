import Mathlib

theorem algebra_176918 (a b c : ℝ) (h₀ : a * 1 + b * 2 + c * 1 * 2 = 3)
    (h₁ : a * 2 + b * 3 + c * 2 * 3 = 4) (d : ℝ) (hd : d ≠ 0)
    (h₂ : ∀ x, a * x + b * d + c * x * d = x) :
    d = 4 := by

  have eq1 := h₂ 0
  have h₃ : b * d = 0 := by
    linarith

  have h₄ : b = 0 := by
    cases' (mul_eq_zero.mp h₃) with hb1 hb2
    · exact hb1 -- Case where b = 0
    · -- Case where d = 0
      exfalso
      apply hd
      exact hb2 -- This yields h : d = 0, which contradicts hd : d ≠ 0

  rw [h₄] at h₀ h₁

  have eq3 : a + 2 * c = 3 := by
    linarith

  have eq4 : 2 * a + 6 * c = 4 := by 
    linarith

  have hc : c = -1 := by
    linarith [eq3, eq4]

  have ha : a = 5 := by
    linarith [eq3, hc]

  have eq5 := h₂ 1
  rw [h₄] at eq5

  rw [ha, hc] at eq5
  linarith