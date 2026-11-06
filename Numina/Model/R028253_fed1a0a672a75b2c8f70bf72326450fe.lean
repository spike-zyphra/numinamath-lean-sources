import Mathlib

open BigOperators Real Set

theorem algebra_9390 {f : ℝ → ℝ} (hf : f = λ x => 2 * x - log x) :
    MonotoneOn f (Ioi (1 / 2)) := by
  intro x hx y hy hxy
  have h1 : x > 1 / 2 := by
    simpa using hx
  have h2 : y > 1 / 2 := by
    simpa using hy
  have h3 : x ≤ y := by linarith
  have h4 : x > 0 := by linarith
  have h5 : y > 0 := by linarith

  have h7 : log y - log x ≤ 2 * (y - x) := by
    have h8 : log y = log (x + (y - x)) := by ring_nf
    rw [h8]
    have h10 : log (x + (y - x)) - log x ≤ 2 * (y - x) := by
      have h11 : log (x + (y - x)) = log (x * (1 + (y - x) / x)) := by
        have h9 : x + (y - x) = x * (1 + (y - x) / x) := by
          field_simp [(show x ≠ 0 by linarith)]
          all_goals nlinarith
        rw [h9]
      have h12 : log (x * (1 + (y - x) / x)) = log x + log (1 + (y - x) / x) := by
        rw [log_mul (by linarith) (by
          have h20 : 1 + (y - x) / x > 0 := by
            have h21 : (y - x) / x ≥ -1 / 2 := by
              apply (le_div_iff₀ (by linarith)).mpr
              nlinarith
            have h22 : (y - x) / x > -1 := by
              linarith
            have h23 : 1 + (y - x) / x > 0 := by
              linarith
            linarith
          linarith
        )]
      have h13 : log (x + (y - x)) - log x = log (1 + (y - x) / x) := by
        rw [h11, h12]
        all_goals
          linarith
      rw [h13]
      have h14 : log (1 + (y - x) / x) ≤ (y - x) / x := by
        have h19 : (1 + (y - x) / x) ≥ 1 := by
          have h30 : (y - x) / x ≥ 0 := by
            apply (le_div_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        have h29 : log (1 + (y - x) / x) ≤ (y - x) / x := by
          have h30 : log (1 + (y - x) / x) ≤ (y - x) / x := by
            have h23 : (1 + (y - x) / x) ≥ 1 := by
              have h30 : (y - x) / x ≥ 0 := by
                apply (le_div_iff₀ (by linarith)).mpr
                nlinarith
              linarith
            have h24 : log (1 + (y - x) / x) ≤ (1 + (y - x) / x) - 1 := by
              linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + (y - x) / x by
                have h20 : 1 + (y - x) / x > 0 := by
                  have h21 : (y - x) / x ≥ -1 / 2 := by
                    apply (le_div_iff₀ (by linarith)).mpr
                    nlinarith
                  have h22 : (y - x) / x > -1 := by
                    linarith
                  have h23 : 1 + (y - x) / x > 0 := by
                    linarith
                  linarith
                linarith
              )]
            have h25 : (1 + (y - x) / x) - 1 = (y - x) / x := by
              field_simp [(show x ≠ 0 by linarith)]
            linarith [h24, h25]
          linarith
        linarith
      have h40 : (y - x) / x ≤ 2 * (y - x) := by
        have h41 : (y - x) / x ≤ 2 * (y - x) := by
          have h42 : y - x ≥ 0 := by nlinarith
          have h43 : x ≥ 1 / 2 := by linarith
          have h44 : x > 0 := by linarith
          have h45 : (y - x) / x ≤ 2 * (y - x) := by
            have h46 : y - x ≥ 0 := by nlinarith
            apply (div_le_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        linarith
      linarith [h14, h40]
    linarith

  have h11 : f x ≤ f y := by
    rw [hf]
    simp
    linarith [h7]
  exact h11