import Mathlib

theorem algebra_123958 {f : ℝ → ℝ} (hf : ∀ x, x ≠ -3 / 2 → f x = c * x / (2 * x + 3))
    (hff : ∀ x, x ≠ -3 / 2 → f (f x) = x) : c = -3 := by

  have eq1 := hff (-3) (by norm_num)

  have h1 : f (-3) = c := by 
    have h2 : f (-3) = c * (-3) / (2 * (-3) + 3) := by 
      apply hf 
      norm_num 
    rw [h2]
    norm_num 
    all_goals field_simp <;> ring

  have eq2 : f (f (-3)) = f c := by 
    rw [h1]

  have eq3 : f c = -3 := by 
    linarith [eq1, eq2]

  by_cases h1 : 2 * c + 3 = 0
  · -- Assume 2 * c + 3 = 0, so c = -3 / 2
    have hc1 : c = -3 / 2 := by linarith
    have eq4 : f c = -3 := eq3
    rw [hc1] at eq4
    have eq5 : f (-3 / 2 : ℝ) = -3 := eq4

    have eq6 : f (1 : ℝ) = c / 5 := by 
      have h5 : f (1 : ℝ) = c * (1 : ℝ) / (2 * (1 : ℝ) + 3) := by 
        apply hf 
        norm_num 
      rw [h5]
      norm_num 
      <;> ring

    have eq7 : f (f (1 : ℝ)) = (1 : ℝ) := by 
      apply hff 
      norm_num

    rw [eq6] at eq7

    have eq8 : f (c / 5) = 1 := eq7

    have eq9 : f (c / 5) = ((c) * (c / 5)) / (2 * (c / 5) + 3) := by 
      apply hf 
      intro h8 
      have h10 : c = -3 / 2 := hc1
      nlinarith

    rw [eq9] at eq8 
    rw [hc1] at eq8 
    field_simp at eq8 
    all_goals norm_num [hc1] at eq8 
  · -- Assume 2 * c + 3 ≠ 0.
    have hc2 : c ≠ -3 / 2 := by 
      intro h5 
      have : 2 * c + 3 = 0 := by linarith 
      contradiction

    have eq4 : f c = c * c / (2 * c + 3) := by 
      apply hf 
      intro h8 
      apply h1 
      linarith

    rw [eq4] at eq3 
    have eq6 : 2 * c + 3 ≠ 0 := by 
      intro h5 
      have : c = -3 / 2 := by linarith 
      contradiction

    have eq7 : c * c / (2 * c + 3) = -3 := eq3 
    have eq8 : c * c = -3 * (2 * c + 3) := by 
      field_simp [eq6] at eq7 
      linarith

    have eq9 : (c + 3) ^ 2 = 0 := by 
      nlinarith

    have eq10 : c + 3 = 0 := by 
      apply pow_eq_zero 
      exact eq9

    linarith