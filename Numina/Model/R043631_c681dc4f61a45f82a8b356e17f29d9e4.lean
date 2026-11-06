import Mathlib


theorem algebra_10865 {a b c d : ℤ} (h : ∀ x : ℝ, (x^2 + a * x + b) * (x^2 + c * x + d) = x^4 + x^3 - 2 * x^2 + 17 * x - 5) :
    a + b + c + d = 5 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1 : ℝ)
  have eq4 := h (2 : ℝ)
  have eq5 := h (-2 : ℝ)
  ring_nf at eq1 eq2 eq3 eq4 eq5
  have h1 : (b : ℝ) * (d : ℝ) = -5 := by
    nlinarith
  have h2 : (1 + (a : ℝ) + (b : ℝ)) * (1 + (c : ℝ) + (d : ℝ)) = 12 := by
    nlinarith
  have h3 : (1 - (a : ℝ) + (b : ℝ)) * (1 - (c : ℝ) + (d : ℝ)) = -24 := by
    nlinarith
  have h4 : (4 + 2 * (a : ℝ) + (b : ℝ)) * (4 + 2 * (c : ℝ) + (d : ℝ)) = 45 := by
    nlinarith
  have h5 : (4 - 2 * (a : ℝ) + (b : ℝ)) * (4 - 2 * (c : ℝ) + (d : ℝ)) = -39 := by
    nlinarith
  have h1' : b * d = -5 := by
    have h11 : (b : ℝ) * (d : ℝ) = -5 := h1
    exact_mod_cast h11
  have h2' : (1 + a + b) * (1 + c + d) = 12 := by
    have h22 : (1 + (a : ℝ) + (b : ℝ)) * (1 + (c : ℝ) + (d : ℝ)) = 12 := h2
    exact_mod_cast h22
  have h3' : (1 - a + b) * (1 - c + d) = -24 := by
    have h33 : (1 - (a : ℝ) + (b : ℝ)) * (1 - (c : ℝ) + (d : ℝ)) = -24 := h3
    exact_mod_cast h33
  have h4' : (4 + 2 * a + b) * (4 + 2 * c + d) = 45 := by
    have h44 : (4 + 2 * (a : ℝ) + (b : ℝ)) * (4 + 2 * (c : ℝ) + (d : ℝ)) = 45 := h4
    exact_mod_cast h44
  have h5' : (4 - 2 * a + b) * (4 - 2 * c + d) = -39 := by
    have h55 : (4 - 2 * (a : ℝ) + (b : ℝ)) * (4 - 2 * (c : ℝ) + (d : ℝ)) = -39 := h5
    exact_mod_cast h55
  have h7 : b = 1 ∨ b = -1 ∨ b = 5 ∨ b = -5 := by
    have h7 : b * d = -5 := h1'
    have h8 : b ∣ -5 := by
      use d
      all_goals linarith
    have h9 : b ∣ 5 := by
      exact Int.dvd_neg.mp h8
    have : b = 1 ∨ b = -1 ∨ b = 5 ∨ b = -5 := by
      have h10 : b ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h9
      have h11 : b ≥ -5 := by
        have h11 : -b ∣ 5 := by
          exact Int.neg_dvd.2 h9
        have h12 : -b ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h11
        omega
      interval_cases b <;> try { tauto }
    assumption
  rcases h7 with h7 | h7 | h7 | h7
  · -- b = 1
    have h8 : d = -5 := by
      rw [show b = 1 by linarith] at h1'
      have : (1 : ℤ) * d = -5 := by linarith
      omega
    rw [show d = -5 by linarith] at h2' h3' h4' h5'
    rw [show b = 1 by linarith] at h2' h3' h4' h5'
    have h8 : a + c = 1 := by
      nlinarith
    have h9 : a * c = 2 := by
      nlinarith
    have h10 : a ≤ 3 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    have h11 : a ≥ -1 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    interval_cases a <;> omega
  · -- b = -1
    have h8 : d = 5 := by
      rw [show b = -1 by linarith] at h1'
      have : (-1 : ℤ) * d = -5 := by linarith
      omega
    rw [show d = 5 by linarith] at h2' h3' h4' h5'
    rw [show b = -1 by linarith] at h2' h3' h4' h5'
    -- Now we can solve relevant equations.
    have h8 : a + c = 1 := by
      nlinarith
    have h9 : a * c = -6 := by
      nlinarith
    have h10 : a ≤ 7 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    have h11 : a ≥ -3 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    interval_cases a <;> omega
  · -- b = 5
    have h8 : d = -1 := by
      rw [show b = 5 by linarith] at h1'
      have : (5 : ℤ) * d = -5 := by linarith
      omega
    rw [show d = -1 by linarith] at h2' h3' h4' h5'
    rw [show b = 5 by linarith] at h2' h3' h4' h5'
    -- Now we can solve relevant equations.
    have h8 : a + c = 1 := by
      nlinarith
    have h9 : a * c = -6 := by
      nlinarith
    have h10 : a ≤ 7 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    have h11 : a ≥ -3 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    interval_cases a <;> omega
  · -- b = -5
    have h8 : d = 1 := by
      rw [show b = -5 by linarith] at h1'
      have : (-5 : ℤ) * d = -5 := by linarith
      omega
    rw [show d = 1 by linarith] at h2' h3' h4' h5'
    rw [show b = -5 by linarith] at h2' h3' h4' h5'
    -- Now we can solve relevant equations.
    have h8 : a + c = 1 := by
      nlinarith
    have h9 : a * c = 2 := by
      nlinarith
    have h10 : a ≤ 3 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    have h11 : a ≥ -1 := by
      nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (a + 2 : ℤ)]
    interval_cases a <;> omega