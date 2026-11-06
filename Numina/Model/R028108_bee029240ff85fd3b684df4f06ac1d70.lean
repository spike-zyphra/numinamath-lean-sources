import Mathlib

open Real


lemma lemma_1 {g : ℝ → ℝ} (h : ∀ x, x ≠ 1 → g x = (x + 2009) / (x - 1)) :
    ∀ x, x ≠ 1 → g (g x) = x := by
  intro x hx
  have hg1 : g x = (x + 2009) / (x - 1) := h x hx
  have hg2 : g (g x) = g ((x + 2009) / (x - 1)) := by
    rw [hg1]
  have hg3 : g ((x + 2009) / (x - 1)) = (( (x + 2009) / (x - 1) ) + 2009) / (( (x + 2009) / (x - 1) ) - 1) := by
    have hx2 : ( (x + 2009) / (x - 1) ) ≠ 1 := by
      by_contra h'
      have h3 : (x + 2009) / (x - 1) = 1 := by linarith
      have hx6 : x - 1 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hx7 : x + 2009 = x - 1 := by
        field_simp [hx6] at h3
        all_goals linarith
      linarith
    apply h
    exact hx2
  rw [hg2, hg3]
  have hx6 : x - 1 ≠ 0 := by
    intro h'
    apply hx
    linarith
  have hx7 : ((x + 2009) / (x - 1) - 1) ≠ 0 := by
    by_contra h'
    have hx6 : x - 1 ≠ 0 := by
      intro h'
      apply hx
      linarith
    have hx8 : (x + 2009) / (x - 1) - 1 = 0 := by
      linarith
    have hx9 : (x + 2009) / (x - 1) = 1 := by linarith
    have hx10 : x + 2009 = x - 1 := by
      field_simp [show x - 1 ≠ 0 by
        intro h'
        apply hx
        linarith
      ] at hx9 ⊢
      all_goals linarith
    linarith
  have eq1 : ((x + 2009) / (x - 1) + 2009) / ((x + 2009) / (x - 1) - 1) = x := by
    have eq2 : ((x + 2009) / (x - 1) + 2009) = x * ((x + 2009) / (x - 1) - 1) := by
      field_simp [hx6, hx7] at *
      <;> ring_nf
    have hx8 : ((x + 2009) / (x - 1) - 1) ≠ 0 := hx7
    field_simp [hx8] at eq2 ⊢
    all_goals linarith [eq2]
  linarith [eq1]


theorem algebra_32591 (f : ℝ → ℝ) :
    (∀ x, x ≠ 1 → x + f x + 2 * f ((x + 2009) / (x - 1)) = 2010) ↔
    ∀ x, x ≠ 1 → f x = (x + 2010 - 2 * (x + 2009) / (x - 1)) / 3 := by
  constructor
  · -- Assume functional equation, prove explicit form
    intro h
    intro x hx
    have eq1 : x + f x + 2 * f ((x + 2009) / (x - 1)) = 2010 := h x hx
    have h2 : ( (x + 2009) / (x - 1) ) ≠ 1 := by
      by_contra h'
      have h3 : (x + 2009) / (x - 1) = 1 := by linarith
      have hx6 : x - 1 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hx7 : x + 2009 = x - 1 := by
        field_simp [hx6] at h3
        all_goals linarith
      linarith
    have eq2 : ( (x + 2009) / (x - 1) ) + f ((x + 2009) / (x - 1)) + 2 * f (( ( (x + 2009) / (x - 1) ) + 2009 ) / ( ( (x + 2009) / (x - 1) ) - 1 )) = 2010 := by
      apply h
      intro h_eq
      have h4 : ( (x + 2009) / (x - 1) ) = 1 := by
        linarith [h_eq]
      contradiction
    have hx5 : (( (x + 2009) / (x - 1) ) + 2009 ) / ( ( (x + 2009) / (x - 1) ) - 1 ) = x := by
      have hx6 : x - 1 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hx7 : ((x + 2009) / (x - 1) - 1) ≠ 0 := by
        by_contra h'
        have hx8 : (x + 2009) / (x - 1) - 1 = 0 := by
          linarith
        have hx9 : (x + 2009) / (x - 1) = 1 := by linarith
        have hx10 : x + 2009 = x - 1 := by
          field_simp [show x - 1 ≠ 0 by
            intro h'
            apply hx
            linarith
          ] at hx9 ⊢
          all_goals linarith
        linarith
      field_simp [hx6, hx7] at *
      <;> ring_nf
    rw [hx5] at eq2
    have eq3 : f x = (2010 + x - 2 * ((x + 2009) / (x - 1)) ) / 3 := by
      linarith [eq1, eq2]
    have hx2 : f x = (x + 2010 - 2 * (x + 2009) / (x - 1)) / 3 := by
      rw [eq3]
      ring_nf
    exact hx2
  · -- Assume explicit form, prove functional equation
    intro h x hx
    have hfx : f x = (x + 2010 - 2 * (x + 2009) / (x - 1)) / 3 := by
      apply h x hx
    have h2 : ( (x + 2009) / (x - 1) ) ≠ 1 := by
      by_contra h'
      have h3 : (x + 2009) / (x - 1) = 1 := by linarith
      have hx6 : x - 1 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hx7 : x + 2009 = x - 1 := by
        field_simp [hx6] at h3
        all_goals linarith
      linarith
    have hfgx : f ((x + 2009) / (x - 1)) = (( (x + 2009) / (x - 1) ) + 2010 - 2 * ( ((x + 2009) / (x - 1) ) + 2009 ) / ( ((x + 2009) / (x - 1) ) - 1 ) ) / 3 := by
      apply h ((x + 2009) / (x - 1)) 
      intro h_eq
      have h4 : ( (x + 2009) / (x - 1) ) = 1 := by
        linarith [h_eq]
      contradiction
    rw [hfx, hfgx]
    have hx5 : (( (x + 2009) / (x - 1) ) + 2009 ) / ( ( (x + 2009) / (x - 1) ) - 1 ) = x := by
      have hx6 : x - 1 ≠ 0 := by
        intro h'
        apply hx
        linarith
      have hx7 : ((x + 2009) / (x - 1) - 1) ≠ 0 := by
        by_contra h'
        have hx8 : (x + 2009) / (x - 1) - 1 = 0 := by
          linarith
        have hx9 : (x + 2009) / (x - 1) = 1 := by linarith
        have hx10 : x + 2009 = x - 1 := by
          field_simp [show x - 1 ≠ 0 by
            intro h'
            apply hx
            linarith
          ] at hx9 ⊢
          all_goals linarith
        linarith
      field_simp [hx6, hx7] at *
      <;> ring_nf
    field_simp [hx5, show x - 1 ≠ 0 by intro h'; apply hx; linarith] at *
    ring_nf