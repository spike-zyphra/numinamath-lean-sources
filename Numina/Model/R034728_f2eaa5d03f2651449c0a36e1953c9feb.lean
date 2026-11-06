import Mathlib

theorem algebra_5349 {d : ℤ} (hd : d > 0) (hdd : ¬ ∃ n : ℕ, n^2 = d) (r s t u : ℚ)
    (h : r + s * Real.sqrt d = t + u * Real.sqrt d) : r = t ∧ s = u := by
  have h1 : (r : ℝ) - (t : ℝ) + ((s : ℝ) - (u : ℝ)) * Real.sqrt d = 0 := by
    have eq1 : (r : ℝ) + (s : ℝ) * Real.sqrt d = (t : ℝ) + (u : ℝ) * Real.sqrt d := by
      exact_mod_cast h 
    nlinarith

  have eq3 : (r - t : ℝ) + ((s - u) : ℝ) * Real.sqrt d = 0 := by 
    have h_eq : (r : ℝ) - (t : ℝ) + ((s : ℝ) - (u : ℝ)) * Real.sqrt d = 0 := h1 
    ring_nf at h_eq ⊢ 
    linarith

  by_cases h6 : (s - u : ℚ) = 0 
  · -- Assume h6 : s - u = 0.
    have h7 : (s - u : ℚ) = 0 := h6 
    have h8 : (s - u : ℝ) = 0 := by 
      exact_mod_cast h7

    have eq4 : (r - t : ℝ) = 0 := by 
      rw [h8] at eq3 
      nlinarith 

    have eq5 : (r : ℝ) = (t : ℝ) := by 
      linarith

    have eq6 : r = t := by 
      exact_mod_cast eq5

    have eq7 : s = u := by 
      have h8' : s - u = 0 := by 
        exact_mod_cast h7 
      linarith 

    exact ⟨eq6, eq7⟩

  · -- Assume ¬(s - u : ℚ) = 0 
    have h7 : (s - u : ℚ) ≠ 0 := by 
      intro h8 
      apply h6 
      exact h8 

    have h7' : (s - u : ℝ) ≠ 0 := by 
      exact_mod_cast h7 

    have eq4 : Real.sqrt d = ((t - r) : ℝ) / ((s - u) : ℝ) := by 
      have eq5 : (r - t : ℝ) + ((s - u) : ℝ) * Real.sqrt d = 0 := eq3 
      have eq6 : Real.sqrt d = ((t - r) : ℝ) / ((s - u) : ℝ) := by 
        have eq7' : (s - u : ℝ) ≠ 0 := h7' 
        field_simp [eq7'] 
        nlinarith 
      linarith 

    have h8 : ∃ q : ℚ, Real.sqrt d = (q : ℝ) := by 
      use ((t - r) / (s - u) : ℚ) 
      have eq6' : (Real.sqrt d : ℝ) = ((t - r) : ℝ) / ((s - u) : ℝ) := eq4 
      rw [eq6']
      all_goals 
        simp at *
        <;> norm_num 

    rcases h8 with ⟨q, hq⟩ 
    have h9 : (q : ℝ) ^ 2 = (d : ℝ) := by 
      have h11 : (Real.sqrt d : ℝ) ^ 2 = (d : ℝ) := by 
        rw [Real.sq_sqrt] 
        have h14 : (d : ℝ) ≥ (0 : ℝ) := by 
          have h15 : (d : ℤ) > 0 := hd 
          have h16 : (d : ℤ) ≥ 0 := by linarith 
          exact_mod_cast (show (d : ℤ) ≥ 0 by linarith)
        linarith 
      rw [show Real.sqrt d = (q : ℝ) by linarith [hq]] at h11 
      linarith 

    have h10 : (q ^ 2 : ℚ) = (d : ℤ) := by 
      have h11 : (q : ℝ) ^ 2 = (d : ℝ) := h9 
      exact_mod_cast (show (q : ℝ) ^ 2 = (d : ℝ) by linarith) 

    have h11 : IsSquare (d : ℚ) := by 
      use q 
      linarith

    have h12 : IsSquare (d : ℤ) := by 
      exact_mod_cast h11 

    rcases h12 with ⟨a, ha⟩ 
    have h13 : ∃ n : ℕ, (n : ℕ) ^ 2 = (d : ℤ) := by 
      use a.natAbs 
      have h14 : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by 
        simp [Int.natAbs_sq] 
      have h15 : a ^ 2 = (d : ℤ) := by 
        linarith 
      have h16 : (a.natAbs : ℤ) ^ 2 = (d : ℤ) := by 
        linarith 
      exact_mod_cast h16 
    contradiction