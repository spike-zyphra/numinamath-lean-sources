import Mathlib

theorem algebra_93810 (W X Y Z : ℤ) (h₀ : W ≠ X) (h₁ : W ≠ Y) (h₂ : W ≠ Z)
    (h₃ : X ≠ Y) (h₄ : X ≠ Z) (h₅ : Y ≠ Z) (h₆ : 1 ≤ W ∧ W ≤ 4) (h₇ : 1 ≤ X ∧ X ≤ 4)
    (h₈ : 1 ≤ Y ∧ Y ≤ 4) (h₉ : 1 ≤ Z ∧ Z ≤ 4) (h₁₀ : (W / X : ℝ) - (Y / Z : ℝ) = 1) :
    W + Y = 7 := by
  have eq1 : (W : ℝ) * (Z : ℝ) - (X : ℝ) * (Y : ℝ) = (X : ℝ) * (Z : ℝ) := by
    have eq2 : (W / X : ℝ) - (Y / Z : ℝ) = 1 := h₁₀
    field_simp [(show (X : ℝ) ≠ 0 by
      by_contra h
      have h' : X = 0 := by exact_mod_cast h
      linarith [h₇.1, h₇.2, h']
    ), (show (Z : ℝ) ≠ 0 by
      by_contra h
      have h' : Z = 0 := by exact_mod_cast h
      linarith [h₉.1, h₉.2, h']
    )] at eq2 ⊢
    linarith
  have eq2 : W * Z - X * Y = X * Z := by
    have eq2' : (W * Z : ℝ) - (X * Y : ℝ) = (X * Z : ℝ) := by
      nlinarith [eq1]
    norm_num at eq2' ⊢
    exact_mod_cast eq2'

  have h11 : 1 ≤ W := h₆.1
  have h12 : W ≤ 4 := h₆.2
  have h13 : 1 ≤ X := h₇.1
  have h14 : X ≤ 4 := h₇.2
  have h15 : 1 ≤ Y := h₈.1
  have h16 : Y ≤ 4 := h₈.2
  have h17 : 1 ≤ Z := h₉.1
  have h18 : Z ≤ 4 := h₉.2

  interval_cases W <;> interval_cases X <;> interval_cases Y <;> interval_cases Z <;> norm_num at eq2 h₀ h₁ h₂ h₃ h₄ h₅ <;> omega