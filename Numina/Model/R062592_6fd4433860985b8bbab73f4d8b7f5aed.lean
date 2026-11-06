import Mathlib

theorem inequalities_601389 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) ≥ (a + b + c) / 2 := by
  have h₀ : 0 < b + c := by positivity
  have h₁ : 0 < c + a := by positivity
  have h₂ : 0 < a + b := by positivity

  have h₄ : a ^ 2 / (b + c) + (b + c) / 4 ≥ a := by
    have h₅ : a ^ 2 / (b + c) + (b + c) / 4 - a ≥ 0 := by
      have : a ^ 2 / (b + c) + (b + c) / 4 - a = (2 * a - (b + c)) ^ 2 / (4 * (b + c)) := by
        field_simp
        ring
      rw [this]
      positivity
    linarith

  have h₆ : b ^ 2 / (c + a) + (c + a) / 4 ≥ b := by
    have h₇ : b ^ 2 / (c + a) + (c + a) / 4 - b ≥ 0 := by
      have : b ^ 2 / (c + a) + (c + a) / 4 - b = (2 * b - (c + a)) ^ 2 / (4 * (c + a)) := by
        field_simp
        ring
      rw [this]
      positivity
    linarith

  have h₈ : c ^ 2 / (a + b) + (a + b) / 4 ≥ c := by
    have h₉ : c ^ 2 / (a + b) + (a + b) / 4 - c ≥ 0 := by
      have : c ^ 2 / (a + b) + (a + b) / 4 - c = (2 * c - (a + b)) ^ 2 / (4 * (a + b)) := by
        field_simp
        ring
      rw [this]
      positivity
    linarith
  
  have h₅ : (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) + ((b + c) / 4 + (c + a) / 4 + (a + b) / 4) ≥ a + b + c := by linarith
  have h₆ : (b + c) / 4 + (c + a) / 4 + (a + b) / 4 = (a + b + c) / 2 := by linarith
  linarith