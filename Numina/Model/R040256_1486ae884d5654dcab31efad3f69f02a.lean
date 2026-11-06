import Mathlib

theorem algebra_145979 (a b c : ℝ) (h₀ : a * b + c = 2) (h₁ : a * c + b = 2) (h₂ : b * c + a = 2) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = -2 ∧ b = -2 ∧ c = -2) := by
  have eq1 : (a - 1) * (b - c) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h3 h4
  · -- Case $a - 1 = 0$
    have ha1 : a = 1 := by linarith
    have eq2 : b + c = 2 := by
      rw [ha1] at h₀
      linarith
    have eq3 : b * c = 1 := by
      rw [ha1] at h₂
      linarith
    have hb1 : b = 1 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hc1 : c = 1 := by
      nlinarith [hb1, eq2]
    left
    constructor
    · exact ha1
    constructor
    · exact hb1
    · exact hc1
  · -- Case $b - c = 0$
    have h_eq : b = c := by linarith
    have eq1' : a * b + b = 2 := by
      have h3' : c = b := by linarith
      rw [h3'] at h₀
      linarith
    have eq2' : b ^ 2 + a = 2 := by
      have h3' : c = b := by linarith
      rw [h3'] at h₂
      nlinarith
    have eq3' : b * (a + 1) = 2 := by
      nlinarith [eq1']
    have eq4' : a = 2 - b ^ 2 := by
      linarith [eq2']
    rw [eq4'] at eq3'
    have eq5' : b * ((2 - b ^ 2) + 1) = 2 := eq3'
    have eq6' : b ^ 3 - 3 * b + 2 = 0 := by
      nlinarith [eq5']
    have eq7' : (b - 1) ^ 2 * (b + 2) = 0 := by 
      nlinarith [eq6']
    cases' (mul_eq_zero.mp eq7') with h8 h9
    · -- Case where $(b - 1)^2 = 0$, so $b = 1$
      have hb1 : b = 1 := by 
        nlinarith [pow_eq_zero (show (b - 1) ^ 2 = 0 by linarith)]
      have ha1 : a = 1 := by
        nlinarith [hb1, eq2']
      left
      constructor
      · exact ha1
      constructor
      · exact hb1
      · -- Show c = 1
        nlinarith [hb1, h_eq]
    · -- Case where $b + 2 = 0$, so $b = -2$
      have hb2 : b = -2 := by linarith
      have ha2 : a = -2 := by
        nlinarith [hb2, eq2']
      right
      constructor
      · exact ha2
      constructor
      · exact hb2
      · -- Show c = -2
        nlinarith [hb2, h_eq]