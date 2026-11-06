import Mathlib

theorem algebra_171582 (a b c : ℝ) (h₀ : Real.log 0.021 = 2 * a + b + c - 3)
    (h₁ : Real.log 0.27 = 6 * a - 3 * b - 2) (h₂ : Real.log 1.5 = 3 * a - b + c)
    (h₃ : Real.log 2.8 = 1 - 2 * a + 2 * b - c) (h₄ : Real.log 3 = 2 * a - b)
    (h₅ : Real.log 5 = a + c) (h₆ : Real.log 6 = 1 + a - b - c) (h₇ : Real.log 7 = 2 * b + 3)
    (h₈ : Real.log 8 = 3 - 3 * a - 3 * c) (h₉ : Real.log 9 = 4 * a - 2 * b)
    (h₁₀ : Real.log 14 = 1 - c + 2 * b) :
    Real.log 7 = 2 * b + 3 ∧ Real.log 1.5 = 3 - b - 1 := by

  constructor
  · -- Show that Real.log 7 = 2 * b + 3 
    exact h₇
  · -- Show that Real.log 1.5 = 3 - b - 1 
    have h1_5 : Real.log 1.5 = Real.log 3 - Real.log 2 := by 
      have h1 : Real.log 1.5 = Real.log (3 / 2) := by 
        norm_num 
      have h2 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by 
        rw [Real.log_div (by norm_num) (by norm_num)]
      linarith [h1, h2]
    have h2_eq : Real.log 2 = 1 - a - c := by 
      have h6 : Real.log 6 = 1 + a - b - c := h₆ 
      have h3 : Real.log 3 = 2 * a - b := h₄ 
      have h2' : Real.log 6 = Real.log 2 + Real.log 3 := by 
        have h6' : Real.log 6 = Real.log (2 * 3) := by 
          norm_num 
        rw [h6']
        rw [Real.log_mul (by norm_num) (by norm_num)]
      linarith [h2', h6, h3]
    have eq1 : Real.log 1.5 = 3 * a - b + c := h₂ 
    have eq2 : Real.log 1.5 = Real.log 3 - Real.log 2 := h1_5 
    rw [h2_eq, h₄] at eq2 
    linarith [eq1, eq2]