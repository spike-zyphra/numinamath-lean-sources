import Mathlib

theorem algebra_4663 {x y : ℕ} (h : x^2 - y^2 = 29) : x = 15 := by
  have h1 : x^2 = y^2 + 29 := by
    omega

  have h2 : x > y := by
    by_contra h2
    push_neg at h2
    have h3 : y ≥ x := by linarith
    have h4 : x^2 ≤ y^2 := by
      have h5 : y ≥ x := by linarith
      have : x^2 ≤ y^2 := by nlinarith
      linarith
    nlinarith

  have h4 : x ≤ 15 := by
    by_contra h4
    push_neg at h4
    have h5 : y < x := by
      nlinarith
    have h6 : y ≤ 15 := by
      nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    interval_cases y <;> try { 
      have h10 : x ≤ 32 := by
        nlinarith
      interval_cases x <;> omega
    }

  have h4' : x ≥ 15 := by
    by_contra h5
    push_neg at h5
    have h7 : x ≤ 14 := by
      omega
    have h8 : y ≤ 14 := by
      nlinarith
    interval_cases x <;> try { 
      interval_cases y <;> omega
    }

  have h6 : x = 15 := by
    linarith
  exact h6