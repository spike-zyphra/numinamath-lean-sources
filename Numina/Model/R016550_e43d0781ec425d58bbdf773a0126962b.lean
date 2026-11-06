import Mathlib

open Real
open scoped BigOperators

theorem calculus_11892 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a = 7) (h₄ : b = 8) (h₅ : cos (120 * π / 180) = (a^2 + b^2 - c^2) / (2*a*b)) :
  c = 13 := by
  -- Show that cos(120°) = -1/2.
  have h₆ : cos (120 * π / 180) = -1 / 2 := by
    have h₁ : 120 * π / 180 = π - π / 3 := by 
      linarith [Real.pi_pos]
    rw [h₁]
    have h₂ : cos (π - π / 3) = -1 / 2 := by
      have hcos : cos (π - π / 3) = -cos (π / 3) := by
        rw [cos_pi_sub]
      rw [hcos]
      have hcos2 : cos (π / 3) = 1 / 2 := by
        exact cos_pi_div_three
      rw [hcos2]
      <;> linarith
    exact h₂
  -- Substitute the values a=7, b=8 and cos(120°)=-1/2 into the equation h₅
  rw [h₆] at h₅
  rw [h₃] at h₅
  rw [h₄] at h₅
  -- Simplify the equation to find c
  have h₇ : (7:ℝ)^2 + (8:ℝ)^2 - c^2 = -56 := by 
    field_simp at h₅ ⊢
    nlinarith [h₅, Real.pi_pos]
  -- From h₇: 49 + 64 - c^2 = -56 → 113 - c^2 = -56 → c^2 = 169
  have h₈ : c ^ 2 = 169 := by 
    nlinarith [h₇]
  -- Since c > 0, take the square root to get c = 13
  have h₉ : c = 13 := by
    nlinarith [h₈, show c > 0 by linarith]
  exact h₉