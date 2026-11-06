import Mathlib

open Real Set
open scoped Real

theorem algebra_3670 {θ : ℝ} (hθ : θ = arctan (5 / 2)) :
    ∀ x, 5 * cos x + 2 * sin x = 1 ↔ sin (θ + x) = 1 / sqrt 29 := by
  intro x
  constructor
  · -- Assume 5 * cos x + 2 * sin x = 1, prove sin (θ + x) = 1 / sqrt 29
    intro h
    have h1 : cos θ = 2 / sqrt 29 := by
      rw [hθ]
      have : cos (arctan (5 / 2)) = 2 / Real.sqrt 29 := by
        rw [cos_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      exact this
    have h2 : sin θ = 5 / Real.sqrt 29 := by
      rw [hθ]
      have : sin (arctan (5 / 2)) = 5 / Real.sqrt 29 := by
        rw [sin_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      exact this
    have eq1 : sin (θ + x) = (5 / sqrt 29) * cos x + (2 / sqrt 29) * sin x := by 
      rw [sin_add]
      rw [h1, h2]
      <;> field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (29 : ℝ) by norm_num)]
      <;> ring
    have eq2 : sin (θ + x) = 1 / sqrt 29 := by
      have h3 : 5 * cos x + 2 * sin x = 1 := h
      have eq3 : (5 / sqrt 29) * cos x + (2 / sqrt 29) * sin x = (5 * cos x + 2 * sin x) / sqrt 29 := by
        field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (29 : ℝ) by norm_num)]
        <;> ring
      rw [eq3] at eq1
      rw [h3] at eq1
      have : (1 : ℝ) / sqrt 29 = 1 / sqrt 29 := by rfl
      linarith
    exact eq2
  · -- Assume sin (θ + x) = 1 / sqrt 29, prove 5 * cos x + 2 * sin x = 1
    intro h
    have h1 : cos θ = 2 / sqrt 29 := by
      rw [hθ]
      have : cos (arctan (5 / 2)) = 2 / Real.sqrt 29 := by
        rw [cos_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      exact this
    have h2 : sin θ = 5 / Real.sqrt 29 := by
      rw [hθ]
      have : sin (arctan (5 / 2)) = 5 / Real.sqrt 29 := by
        rw [sin_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      exact this
    have eq1 : sin (θ + x) = (5 / sqrt 29) * cos x + (2 / sqrt 29) * sin x := by 
      rw [sin_add]
      rw [h1, h2]
      <;> field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (29 : ℝ) by norm_num)]
      <;> ring
    have h3 : sin (θ + x) = 1 / sqrt 29 := h
    have eq4 : (5 / sqrt 29) * cos x + (2 / sqrt 29) * sin x = 1 / sqrt 29 := by 
      linarith [eq1, h3]
    have h4 : 5 * cos x + 2 * sin x = 1 := by
      have eq3 : (5 / sqrt 29) * cos x + (2 / sqrt 29) * sin x = (5 * cos x + 2 * sin x) / sqrt 29 := by
        field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (29 : ℝ) by norm_num)]
        <;> ring
      rw [eq3] at eq4
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (29 : ℝ) by norm_num)] at eq4 ⊢
      <;> linarith
    exact h4