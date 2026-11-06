import Mathlib

open Real Set
open scoped Real

theorem algebra_138031 (x : ℝ) :
  cos x + cos (x + 2 * π / 3) + cos (x + 4 * π / 3) = 0 ∧
  sin x + sin (x + 2 * π / 3) + sin (x + 4 * π / 3) = 0 := by
  have h1 : cos x + cos (x + 2 * π / 3) + cos (x + 4 * π / 3) = 0 := by
    have hcos1 : cos (x + 2 * π / 3) = cos x * cos (2 * π / 3) - sin x * sin (2 * π / 3) := by
      rw [cos_add]
    have hcos2 : cos (x + 4 * π / 3) = cos x * cos (4 * π / 3) - sin x * sin (4 * π / 3) := by
      rw [cos_add]
    have hcos3 : cos (2 * π / 3) = -1 / 2 := by
      have h1 : 2 * π / 3 = π - π / 3 := by linarith [Real.pi_pos]
      rw [h1]
      rw [cos_pi_sub]
      rw [Real.cos_pi_div_three]
      all_goals linarith
    have hsin3 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h1 : 2 * π / 3 = π - π / 3 := by linarith [Real.pi_pos]
      rw [h1]
      rw [sin_pi_sub]
      rw [Real.sin_pi_div_three]
      all_goals linarith
    have hcos4 : cos (4 * π / 3) = -1 / 2 := by
      have h1 : 4 * π / 3 = π + π / 3 := by nlinarith [Real.pi_pos]
      rw [h1]
      rw [cos_add]
      rw [cos_pi, sin_pi]
      have hcos : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
      have hsin : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [hcos, hsin]
      all_goals linarith
    have hsin4 : sin (4 * π / 3) = -Real.sqrt 3 / 2 := by
      have h1 : 4 * π / 3 = π + π / 3 := by nlinarith [Real.pi_pos]
      rw [h1]
      rw [sin_add]
      rw [sin_pi, cos_pi]
      have hcos : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
      have hsin : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [hsin, hcos]
      all_goals ring
    rw [hcos1, hcos2, hcos3, hsin3, hcos4, hsin4]
    ring
  have h2 : sin x + sin (x + 2 * π / 3) + sin (x + 4 * π / 3) = 0 := by
    have hsin1 : sin (x + 2 * π / 3) = sin x * cos (2 * π / 3) + cos x * sin (2 * π / 3) := by
      rw [sin_add]
    have hsin2 : sin (x + 4 * π / 3) = sin x * cos (4 * π / 3) + cos x * sin (4 * π / 3) := by
      rw [sin_add]
    have hcos3 : cos (2 * π / 3) = -1 / 2 := by
      have h1 : 2 * π / 3 = π - π / 3 := by linarith [Real.pi_pos]
      rw [h1]
      rw [cos_pi_sub]
      rw [Real.cos_pi_div_three]
      all_goals linarith
    have hsin3 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h1 : 2 * π / 3 = π - π / 3 := by linarith [Real.pi_pos]
      rw [h1]
      rw [sin_pi_sub]
      rw [Real.sin_pi_div_three]
      all_goals linarith
    have hcos4 : cos (4 * π / 3) = -1 / 2 := by
      have h1 : 4 * π / 3 = π + π / 3 := by nlinarith [Real.pi_pos]
      rw [h1]
      rw [cos_add]
      rw [cos_pi, sin_pi]
      have hcos : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
      have hsin : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [hcos, hsin]
      all_goals linarith
    have hsin4 : sin (4 * π / 3) = -Real.sqrt 3 / 2 := by
      have h1 : 4 * π / 3 = π + π / 3 := by nlinarith [Real.pi_pos]
      rw [h1]
      rw [sin_add]
      rw [sin_pi, cos_pi]
      have hcos : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
      have hsin : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [hsin, hcos]
      all_goals ring
    rw [hsin1, hsin2, hcos3, hsin3, hcos4, hsin4]
    ring
  exact ⟨h1, h2⟩