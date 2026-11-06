import Mathlib

theorem algebra_282072 {a b c : ℝ} (h₀ : a * b * c = 1) (h₁ : a + b + c = 2)
    (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 3) :
    1 / (a * b + c - 1) + 1 / (b * c + a - 1) + 1 / (c * a + b - 1) = -2 / 3 := by
  have h₃ : a * b + b * c + c * a = 1 / 2 := by
    have eq1 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h₁, h₂] at eq1
    linarith
  have eq1 : a * b + c - 1 = (a - 1) * (b - 1) := by
    have hc : c = 2 - a - b := by linarith
    rw [hc]
    nlinarith
  have eq2 : b * c + a - 1 = (b - 1) * (c - 1) := by
    have ha : a = 2 - b - c := by linarith
    rw [ha]
    nlinarith
  have eq3 : c * a + b - 1 = (c - 1) * (a - 1) := by
    have hb : b = 2 - a - c := by linarith
    rw [hb]
    nlinarith
  rw [eq1, eq2, eq3]
  have h₄ : (a - 1) * (b - 1) * (c - 1) = 3 / 2 := by
    have h₃ : a * b + b * c + c * a = 1 / 2 := h₃
    have h₆ : a + b + c = 2 := h₁
    have h₇ : a * b * c = 1 := h₀
    have eq3 : (a - 1) * (b - 1) * (c - 1) = (a * b * c) - (a * b + b * c + c * a) + (a + b + c) - 1 := by ring
    rw [eq3]
    rw [h₀, h₃, h₆]
    norm_num
  have h₉ : (a - 1) ≠ 0 := by
    by_contra h
    have h₉ : a = 1 := by linarith
    rw [h₉] at h₀ h₁ h₃
    nlinarith
  have h₇ : (b - 1) ≠ 0 := by
    by_contra h
    have h₇ : b = 1 := by linarith
    rw [h₇] at h₀ h₁ h₃
    nlinarith
  have h₆ : (c - 1) ≠ 0 := by
    by_contra h
    have h₆ : c = 1 := by linarith
    rw [h₆] at h₀ h₁ h₃
    nlinarith
  field_simp [(show (a - 1) ≠ 0 by assumption), (show (b - 1) ≠ 0 by assumption), (show (c - 1) ≠ 0 by assumption), 
    show (a - 1) * (b - 1) ≠ 0 by 
      apply mul_ne_zero 
      · assumption
      · assumption, 
    show (b - 1) * (c - 1) ≠ 0 by
      apply mul_ne_zero 
      · assumption
      · assumption, 
    show (c - 1) * (a - 1) ≠ 0 by
      apply mul_ne_zero 
      · assumption
      · assumption
    ]
  <;> nlinarith [h₄, h₁]