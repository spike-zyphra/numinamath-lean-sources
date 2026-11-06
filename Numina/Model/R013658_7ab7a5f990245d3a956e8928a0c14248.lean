import Mathlib

theorem algebra_102201 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 1 → f x = x / (1 - x)) (y x : ℝ)
    (hy : y = f x) (hx : x ≠ 1) : x = -f (-y) := by

  have hfx : y = x / (1 - x) := by
    rw [hy]
    specialize hf x hx
    simpa using hf

  have h1 : x = y / (1 + y) := by
    have eq1 : y = x / (1 - x) := hfx
    have hx1 : x ≠ 1 := hx
    have hx2 : (1 - x) ≠ 0 := by
      intro h
      apply hx1
      linarith

    have eq2 : y * (1 - x) = x := by
      have eq1' : y = x / (1 - x) := hfx
      field_simp [hx2] at eq1' ⊢
      linarith

    have h1ne : 1 + y ≠ 0 := by
      by_contra h
      have eq3 : y = -1 := by
        linarith
      rw [eq3] at eq2
      have eq4 : -1 * (1 - x) = x := by
        linarith
      have eq5 : -1 + x = x := by
        linarith
      have eq6 : -1 = 0 := by
        linarith
      linarith

    have eq5 : y = x * (1 + y) := by
      nlinarith [eq2]

    field_simp [h1ne] at eq5 ⊢
    nlinarith

  have h2 : -f (-y) = y / (1 + y) := by
    have h1ne : 1 + y ≠ 0 := by
      by_contra h
      have eq3 : y = -1 := by
        linarith
      rw [eq3] at hfx
      have eq4 : x / (1 - x) = -1 := by
        linarith
      have h0 : 1 - x ≠ 0 := by
        intro h'
        apply hx
        linarith
      field_simp [h0] at eq4
      all_goals
        nlinarith

    have h4 : -y ≠ 1 := by
      by_contra h
      have eq3 : y = -1 := by
        linarith
      rw [eq3] at hfx
      have eq4 : x / (1 - x) = -1 := by
        linarith
      have h0 : 1 - x ≠ 0 := by
        intro h'
        apply hx
        linarith
      field_simp [h0] at eq4
      all_goals
        nlinarith

    have eq6 : f (-y) = -y / (1 - (-y)) := by
      apply hf
      exact h4

    have eq7 : f (-y) = -y / (1 + y) := by
      rw [eq6]
      ring

    rw [eq7]
    field_simp [h1ne]
    all_goals
      nlinarith

  rw [h2] at *
  exact h1