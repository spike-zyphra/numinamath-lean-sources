import Mathlib

theorem number_theory_294679 (r q : ℚ) (hr : 0 < r) (hq : r < q)
    (hqr : ∃ p : ℚ, Real.sqrt q - Real.sqrt r = p) :
    ∃ a b : ℚ, Real.sqrt q = a ∧ Real.sqrt r = b := by

  rcases hqr with ⟨p, hp⟩
  have h1 : Real.sqrt q = Real.sqrt r + (p : ℝ) := by linarith
  have h2 : Real.sqrt q ^ 2 = (Real.sqrt r + (p : ℝ)) ^ 2 := by
    rw [h1]

  have h3 : Real.sqrt q ^ 2 = (q : ℝ) := by
    have h4 : (q : ℝ) ≥ 0 := by
      have hq' : (q : ℝ) > (0 : ℝ) := by
        exact_mod_cast show (0 : ℚ) < q by linarith
      linarith
    rw [Real.sq_sqrt]
    exact_mod_cast h4

  have h4 : Real.sqrt r ^ 2 = (r : ℝ) := by
    have h5 : (r : ℝ) ≥ 0 := by
      have h6 : (r : ℝ) > (0 : ℝ) := by
        exact_mod_cast show (0 : ℚ) < r by linarith
      linarith
    rw [Real.sq_sqrt]
    exact_mod_cast h5

  have h5 : (Real.sqrt r + (p : ℝ)) ^ 2 = Real.sqrt r ^ 2 + 2 * Real.sqrt r * (p : ℝ) + (p : ℝ) ^ 2 := by ring
  rw [h5] at h2
  rw [h3] at h2

  by_cases hp0 : (p : ℝ) = 0
  · 
    have h7 : Real.sqrt q = Real.sqrt r := by
      linarith [hp0, h1]
    have h8 : Real.sqrt q ^ 2 = Real.sqrt r ^ 2 := by
      rw [h7]
    rw [h3, h4] at h8
    have h9 : (q : ℝ) = (r : ℝ) := by linarith
    have h10 : q = r := by exact_mod_cast h9
    linarith
  · 
    have hp0' : (p : ℝ) ≠ 0 := by
      exact hp0
    have h10 : Real.sqrt r = ( (q : ℝ) - (r : ℝ) - (p : ℝ)^2 ) / (2 * (p : ℝ)) := by
      have h7 : (q : ℝ) = Real.sqrt r ^ 2 + 2 * Real.sqrt r * (p : ℝ) + (p : ℝ) ^ 2 := by
        nlinarith [h2, h4]
      have h8 : (q : ℝ) - (r : ℝ) - (p : ℝ) ^ 2 = 2 * (p : ℝ) * Real.sqrt r := by
        nlinarith [h7, h4]
      have h9 : (p : ℝ) ≠ 0 := hp0
      have h10 : Real.sqrt r = ( (q : ℝ) - (r : ℝ) - (p : ℝ)^2 ) / (2 * (p : ℝ)) := by
        field_simp [(show (2 * (p : ℝ)) ≠ 0 by
          intro h
          have : (p : ℝ) = 0 := by
            linarith
          tauto
        )] at *
        nlinarith
      exact h10

    -- sqrt(r) can be expressed as a rational expression of q, r, p
    -- sqrt(r) = (q - r - p^2) / (2p)
    have h11 : ∃ b : ℚ, Real.sqrt r = (b : ℝ) := by
      use ( (q - r - p^2) / (2 * p) )
      have h10' : Real.sqrt r = ( (q - r - p^2) / (2 * p) : ℝ ) := by
        exact_mod_cast h10
      exact_mod_cast h10'

    rcases h11 with ⟨b, hb⟩
    have h15 : Real.sqrt q = (b + p : ℝ) := by
      nlinarith [hb, h1]

    have h17 : ∃ a : ℚ, Real.sqrt q = (a : ℝ) := by
      use (b + p)
      exact_mod_cast h15

    rcases h17 with ⟨a, ha⟩
    exact ⟨a, b, by linarith [ha], by linarith [hb]⟩