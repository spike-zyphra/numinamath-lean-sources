import Mathlib

theorem algebra_212669 {f : ℝ → ℝ} (hf : ∀ x, f x - (x - 0.5) * f (-x - 1) = 1) :
    ∀ x, x ≠ -0.5 → f x = 1 / (0.5 + x) ∧ f (-0.5) = 0.5 := by
  intro x hx
  have eq1 := hf x
  have eq2 := hf (-x - 1)
  have eq3 : f x - (x - 0.5) * f (-x - 1) = 1 := by
    simpa using eq1
  have eq4 : f (-x - 1) - ((-x - 1) - 0.5) * f (-(-x - 1) - 1) = 1 := by
    simpa using eq2
  have eq5 : f (-x - 1) - ((-x - 1) - 0.5) * f x = 1 := by
    have h1 : -(-x - 1) - 1 = x := by ring
    rw [h1] at eq4
    linarith
  have eq6 : f (-x - 1) = 1 - (x + 1.5) * f x := by
    ring_nf at eq5 ⊢
    linarith
  rw [eq6] at eq3
  have eq7 : f x * (1 + (x - 0.5) * (x + 1.5)) = (x + 0.5) := by
    ring_nf at eq3 ⊢
    linarith
  have eq8 : (x + 0.5) ≠ 0 := by
    intro h
    apply hx
    have : x = -0.5 := by
      norm_num at h ⊢
      linarith
    assumption
  have eq10 : f (-0.5) = 0.5 := by
    specialize hf (-0.5)
    norm_num at hf ⊢
    linarith
  have eq9 : f x = 1 / (0.5 + x) := by
    have eq11 : (1 + (x - 0.5) * (x + 1.5)) = (x + 0.5) ^ 2 := by
      ring_nf
    rw [eq11] at eq7
    have eq14 : f x * (x + 0.5) = 1 := by
      have hne : (x + 0.5) ≠ 0 := by
        exact_mod_cast eq8
      have eq15 : f x * ((x + 0.5) ^ 2) = (x + 0.5) := by
        simpa using eq7
      have eq16 : f x * (x + 0.5) = 1 := by
        apply (mul_left_inj' hne).mp
        linarith
      assumption
    have eq17 : f x = 1 / (0.5 + x) := by
      have hne : (0.5 + x) ≠ 0 := by
        intro h
        apply hx
        have : x = -0.5 := by
          norm_num at h ⊢
          linarith
        assumption
      have eq18 : f x * (0.5 + x) = 1 := by
        have eq19 : f x * (x + 0.5) = 1 := eq14
        ring_nf at eq19 ⊢
        linarith
      field_simp [hne] at eq18 ⊢
      linarith
    assumption
  constructor
  · exact_mod_cast eq9
  · exact_mod_cast eq10