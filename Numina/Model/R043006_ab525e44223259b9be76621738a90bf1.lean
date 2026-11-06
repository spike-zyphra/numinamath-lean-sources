import Mathlib

theorem algebra_305955 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f ((x - 1) / x) = 1 + x) :
    ∀ x, x ≠ 0 ∧ x ≠ 1 → f x = (x ^ 3 - x ^ 2 - 1) / (2 * x * (x - 1)) := by
  intro x hx
  have hx1' : x ≠ 0 := hx.1
  have hx2' : x ≠ 1 := hx.2
  have hne : x - 1 ≠ 0 := by
    intro h
    apply hx2'
    linarith
  -- Apply the functional equation at x
  have eq1 := hf x ⟨hx1', hx2'⟩
  -- Calculate f's argument for the second equation
  have eq5 : ((x - 1) / x - 1) / ((x - 1) / x) = -1 / (x - 1) := by
    field_simp [hx1', hne]
    <;> ring_nf <;> field_simp [hx1', hne] <;> linarith
  -- Calculate f's argument for the third equation
  have eq7 : ((-1 / (x - 1) - 1)) / (-1 / (x - 1)) = x := by
    field_simp [hx1', hne]
    <;> ring_nf <;> field_simp [hx1', hne] <;> linarith
  -- Apply the functional equation at (x - 1) / x
  have eq2 := hf ((x - 1) / x) ⟨by
    by_contra h
    have : x - 1 = 0 := by
      field_simp [hx1'] at h ⊢
      all_goals
        nlinarith
    contradiction, by
    by_contra h
    have : (x - 1) / x = 1 := by linarith
    have : x - 1 = x := by
      field_simp [hx1'] at this ⊢
      all_goals
        nlinarith
    linarith
  ⟩
  rw [eq5] at eq2
  -- Apply the functional equation at -1 / (x - 1)
  have eq3 := hf (-1 / (x - 1)) ⟨by
    by_contra h
    have : -1 / (x - 1) = 0 := by linarith
    have : -1 = 0 := by
      field_simp [hne] at this ⊢
      all_goals
        nlinarith
    linarith
  , by
    by_contra h
    have : -1 / (x - 1) = 1 := by linarith
    have : -1 = x - 1 := by
      field_simp [hne] at this ⊢
      all_goals
        nlinarith
    have hx0 : x = 0 := by
      linarith
    contradiction
  ⟩
  rw [eq7] at eq3
  -- Solve the equations
  have eq8 : f x = (x ^ 3 - x ^ 2 - 1) / (2 * x * (x - 1)) := by
    field_simp [(show (x : ℝ) ≠ 0 by assumption), (show (x - 1 : ℝ) ≠ 0 by
      intro h
      apply hx2'
      linarith
    )] at eq1 eq2 eq3 ⊢
    ring_nf at eq1 eq2 eq3 ⊢
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by
      intro h
      apply hx2'
      linarith
    )]
    all_goals try { linarith }
  exact eq8