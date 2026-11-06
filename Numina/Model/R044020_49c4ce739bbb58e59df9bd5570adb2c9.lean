import Mathlib

theorem number_theory_26087 {q : ℝ} (hq : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ r : ℝ, (q + a) * r = q + b ∧ (q + b) * r = q + c) :
    ∃ r : ℚ, q = ↑r:= by
  rcases hq with ⟨a, b, c, ha, hb, hc, hab, hbc, hca, r, h1, h2⟩
  have eq1 : (q + (a : ℝ)) * r = q + (b : ℝ) := by
    simpa using h1
  have eq2 : (q + (b : ℝ)) * r = q + (c : ℝ) := by
    simpa using h2

  by_cases hr : r = 0
  · -- r = 0
    rw [hr] at eq1 eq2
    have h3 : q + (b : ℝ) = 0 := by
      nlinarith
    have h4 : q + (c : ℝ) = 0 := by
      nlinarith
    have h9 : (b : ℝ) = (c : ℝ) := by
      nlinarith [h3, h4]
    have h10 : b = c := by
      exact_mod_cast (show (b : ℝ) = (c : ℝ) by linarith)
    exfalso
    exact hbc h10
  · -- r ≠ 0
    have h3 : (q + (b : ℝ)) ^ 2 = (q + (a : ℝ)) * (q + (c : ℝ)) := by
      have h6 : (q + (a : ℝ)) ≠ 0 := by
        by_contra h
        have h7 : (q + (a : ℝ)) = 0 := by linarith
        rw [h7] at eq1
        have h3' : q + (b : ℝ) = 0 := by
          nlinarith
        have h4' : q + (c : ℝ) = 0 := by
          have h7' : (q + (b : ℝ)) * r = q + (c : ℝ) := eq2
          have h10 : (q + (b : ℝ)) = 0 := by
            nlinarith [h3']
          rw [h10] at h7'
          nlinarith
        have h9 : (b : ℝ) = (c : ℝ) := by
          nlinarith [h3', h4']
        have h10 : b = c := by
          exact_mod_cast (show (b : ℝ) = (c : ℝ) by linarith)
        exfalso
        exact hbc h10
      have h7 : (q + (b : ℝ)) ≠ 0 := by
        by_contra h
        have h8 : (q + (b : ℝ)) = 0 := by linarith
        rw [h8] at eq2
        have h9 : q + (c : ℝ) = 0 := by
          nlinarith
        have h10 : (q + (a : ℝ)) * r = 0 := by
          have h11 : (q + (a : ℝ)) * r = q + (b : ℝ) := eq1
          rw [show q + (b : ℝ) = 0 by linarith [h8]] at h11
          linarith
        have h11 : (q + (a : ℝ)) = 0 := by
          apply (mul_left_inj' (show r ≠ 0 by
            exact hr
          )).mp
          linarith
        have h12 : (a : ℝ) = (b : ℝ) := by
          nlinarith [h11, h8]
        have h13 : a = b := by
          exact_mod_cast (show (a : ℝ) = (b : ℝ) by linarith)
        exfalso
        exact hab h13
      have eq3 : (q + (a : ℝ)) * r = q + (b : ℝ) := eq1
      have eq4 : (q + (b : ℝ)) * r = q + (c : ℝ) := eq2
      have h8 : (q + (b : ℝ)) ^ 2 = (q + (a : ℝ)) * (q + (c : ℝ)) := by
        have eq5 : (q + (b : ℝ)) ^ 2 = (q + (a : ℝ)) * (q + (b : ℝ)) * r := by
          calc
            (q + (b : ℝ)) ^ 2 = (q + (b : ℝ)) * (q + (b : ℝ)) := by ring
            _ = (q + (a : ℝ)) * r * (q + (b : ℝ)) := by 
              rw [show (q + (a : ℝ)) * r = q + (b : ℝ) by linarith [eq3]] 
            _ = (q + (a : ℝ)) * (q + (b : ℝ)) * r := by ring
        have eq6 : (q + (a : ℝ)) * (q + (c : ℝ)) = (q + (a : ℝ)) * (q + (b : ℝ)) * r := by
          calc
            (q + (a : ℝ)) * (q + (c : ℝ)) = (q + (a : ℝ)) * ((q + (b : ℝ)) * r) := by 
              rw [show (q + (b : ℝ)) * r = q + (c : ℝ) by linarith [eq4]]
            _ = (q + (a : ℝ)) * (q + (b : ℝ)) * r := by ring
        nlinarith [eq5, eq6]
      exact h8
    have eq4 : q * ((2 * (b : ℝ)) - ((a : ℝ) + (c : ℝ)) ) = (a * c : ℝ) - (b ^ 2 : ℝ) := by
      nlinarith
    -- Now we can conclude $q$ is rational.
    have eq5 : q = ( (a * c : ℝ) - (b ^ 2 : ℝ) ) / ( (2 * (b : ℝ)) - ((a : ℝ) + (c : ℝ)) ) := by
      have h8 : (2 * (b : ℝ) - ((a : ℝ) + (c : ℝ)) ) ≠ 0 := by
        by_contra h
        have h9 : (2 * (b : ℝ) - ((a : ℝ) + (c : ℝ)) ) = 0 := by
          linarith
        have eq6 : (a * c : ℝ) - (b ^ 2 : ℝ) = 0 := by
          have h8 : (2 * (b : ℝ) - ((a : ℝ) + (c : ℝ)) ) = 0 := by
            linarith
          rw [h8] at eq4
          nlinarith
        have eq7 : 2 * (b : ℝ) = (a : ℝ) + (c : ℝ) := by
          linarith
        have eq8 : (a * c : ℝ) = (b : ℝ) ^ 2 := by
          linarith
        have eq9 : ((a : ℝ) - (c : ℝ)) ^ 2 = 0 := by
          have h10 : (a + (c : ℝ)) = 2 * (b : ℝ) := by linarith
          nlinarith
        have eq10 : (a : ℝ) = (c : ℝ) := by
          nlinarith
        have eq11 : a = c := by
          exact_mod_cast (show (a : ℝ) = (c : ℝ) by linarith)
        exfalso
        tauto
      field_simp [h8]
      linarith
    -- Hence $q$ equals the rational number
    refine' ⟨ ((a * c - b ^ 2) : ℚ) / ((2 * (b : ℚ)) - ((a : ℚ) + (c : ℚ)) ), by
      norm_num at eq5 ⊢
      linarith
    ⟩