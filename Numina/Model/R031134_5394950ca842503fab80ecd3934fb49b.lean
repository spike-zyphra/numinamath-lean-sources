import Mathlib

theorem number_theory_7452 (x0 y0 : ℕ) (hx0 : x0 > 0) (hy0 : y0 > 0)
    (hxy : x0 * y0 = x0 + y0) :
    ∀ x y : ℕ, x > 0 → y > 0 → x * y = x + y → x0 ≤ x ∧ y0 ≤ y := by
  intro x y hx hy h

  -- First, establish that x = 2 from h.
  have h1 : x = 2 := by

    -- Proof that x ≤ 2
    have eq1 : x ≤ 2 := by
      by_contra h1
      push_neg at h1
      -- Assume x > 2, derive contradiction
      have h2 : y ≤ 1 := by
        nlinarith [h, h1, sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have h3 : y = 1 := by
        omega
      rw [h3] at h
      linarith

    -- Proof that x ≥ 1 from the original h : x * 1 = 1 + 0 contradicts.
    have eq2 : x ≥ 1 := hx
    interval_cases x <;> omega

  have h2 : y = 2 := by
    rw [h1] at h
    nlinarith

  -- Prove x0 = 2
  have h3 : x0 = 2 := by
    have eq1 : x0 ≤ 2 := by
      have h3 : x0 * y0 = x0 + y0 := hxy
      have hx0' : x0 > 0 := hx0
      have hy0' : y0 > 0 := hy0
      have h1 : x0 > 0 := hx0
      have h2 : y0 > 0 := hy0
      by_contra h1
      push_neg at h1
      have h4 : y0 ≤ 1 := by
        nlinarith [hxy, h1, sq_nonneg (x0 - 1 : ℤ), sq_nonneg (y0 - 1 : ℤ)]
      have h4 : y0 = 1 := by
        omega
      rw [h4] at hxy
      nlinarith
    have eq2 : x0 ≥ 1 := hx0
    interval_cases x0 <;> omega

  have h4 : y0 = 2 := by
    rw [h3] at hxy
    nlinarith

  constructor
  · -- Show x0 ≤ x
    omega
  · -- Show y0 ≤ y
    omega