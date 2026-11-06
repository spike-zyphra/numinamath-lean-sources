import Mathlib

theorem algebra_21360 {A B : ℤ} (h : ∀ x, 3*x^2+14*x+8=(3*x+A)*(x+B)) :
    A - B = -2 := by
  have h1 := h 0
  simp at h1
  have h2 := h 1
  norm_num at h2
  have h3 := h (-1)
  norm_num at h3

  have eq1 : A * B = 8 := by
    linarith

  have eq2 : A + 3 * B = 14 := by
    nlinarith [h1, h2]

  -- Solve for B using the quadratic formula.

  -- Since $A = 2$ and $B =4$ is the only solution, we can bound $B$.

  have hB : B = 4 := by
    have h3 : B ∣ 8 := by 
      use A
      linarith [eq1]
    have h4 : B ≤8 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : B ≥ -8 := by
      have : -B ∣ 8 := by
        use -A
        linarith [eq1]
      have h6 : -B ≤8 := by
        apply Int.le_of_dvd (by norm_num) this
      linarith 
    interval_cases B <;> try { omega }

  have hA : A = 2 := by
    rw [hB] at eq2
    linarith

  linarith [hA, hB]