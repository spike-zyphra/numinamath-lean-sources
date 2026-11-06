import Mathlib

-- Determine all pairs (x, y) of positive integers such that 7x² − 13xy + 7y² = |x − y| + 1.
-- Answer: Either (x, y) = (1, 1) or {x, y} = {m³ + m² − 2m − 1, m³ + 2m² − m − 1} for some positive integer m ≥ 2.

theorem number_theory_24542 (x y : ℤ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≥ y)
    (h : (7 * (x:ℝ) ^ 2 - 13 * x * y + 7 * y ^ 2) ^ ((1 : ℝ) / 3) = |x - y| + 1) :
    (x, y) = (1, 1) ∨ ∃ m : ℤ, m ≥ 2 ∧ x = m ^ 3 + 2 * m ^ 2 - m - 1 ∧
    y = m ^ 3 + m ^ 2 - 2 * m - 1 := by

      -- Step 1: Prove that the left-hand side of the equation is non-negative.
      have hpos : 7 * (x:ℝ) ^ 2 - 13 * x * y + 7 * y ^ 2 ≥ 0 := by
        norm_cast
        nlinarith

      -- Step 2: Simplify the absolute value |x - y| since x ≥ y.
      have : |x - y| = x - y := by refine abs_of_nonneg (by linarith)

      -- Step 3: Substitute the simplified |x - y| into the equation.
      rw [this] at h

      -- Step 4: Rewrite the equation as a cube equation.
      have hxyeq : (7 * (x:ℝ) ^ 2 - 13 * x * y + 7 * y ^ 2) = ((((x - y:ℤ))) + 1) ^ 3 := by
        rw [← h]
        have := Real.rpow_mul hpos ((1:ℝ)/3) 3
        norm_cast at this
        norm_cast
        rw [← this]
        simp
      norm_cast at hxyeq

      -- Step 5: Handle the special case where x = y.
      by_cases heq : x = y
      · rw [heq] at hxyeq
        ring_nf at hxyeq
        -- If x = y, solve for y.
        have : y = 1 := by
          refine Int.eq_one_of_dvd_one ?H ?H'
          · linarith
          · rw [← hxyeq]
            exact Dvd.intro_left (y.pow 1) rfl
        -- Conclude that (x, y) = (1, 1).
        left
        rw [heq,this]

      -- Step 6: Handle the general case where x ≠ y.
      · let n := x - y
        -- Prove that n > 0 since x > y.
        have hnpos : n > 0 := by
          unfold n
          by_contra h
          simp at h
          have : x = y := by linarith
          contradiction

        -- Express x in terms of y and n.
        have heqadd : x = n + y := by omega
        rw [heqadd] at hxyeq
        simp at hxyeq

        -- Step 7: Simplify the equation further.
        have : 4 * (7 * (n + y) ^ 2 - 13 * (n + y) * y + 7 * y ^ 2) = (2*y+n) ^ 2 + 27 * n ^ 2:= by
          ring_nf

        -- Step 8: Analyze the structure of the equation.
        have hyn : (2*y+n) ^ 2 = (n-2)^2*(4*n+1) := by
          calc
            _ = (2*y+n) ^ 2 + 27 * n ^ 2 - 27 * n ^ 2:= by ring_nf
            _ = 4 * (n+1) ^ 3 - 27 * n ^ 2 := by rw [← this, hxyeq]
            _ = _ := by ring_nf

        -- Step 9: Consider the case when n = 1.
        by_cases hn1 : n = 1
        · rw [hn1] at hyn
          simp at hyn
          have : y ≥ 1 := by linarith
          have : (2 * y + 1)^2 ≥ 9 := by nlinarith
          linarith

        -- Step 10: Consider the case when n = 2.
        · by_cases hn2 : n = 2
          · rw [hn2] at hyn
            simp at hyn
            linarith

        -- Step 11: Handle the general case where n ≥ 3.
          · have hge3 : n ≥ 3 := by omega
            -- Assume n is at least 3 for this case.
            have hyneq : ((2*y+n) :ℚ) ^ 2 = (n-2)^2*(4*n+1) := by norm_cast
            -- Rewrite the equation in terms of rational numbers.
            have : (4 * n + 1) = (((2 * y + n) : ℚ)/ (n - 2)) ^ 2 := by
              symm
              calc
                _ = ((2 * y + n) :ℚ) ^ 2 / (↑n - 2) ^ 2 := by
                  apply div_pow
                _ = _ := by
                  rw [hyneq, mul_div_cancel_left₀]
                  intro heq2
                  norm_cast at heq2
                  rw [heq2] at hyn
                  simp at hyn
                  linarith
            -- Define q as the rational expression derived from the equation.
            let q := ((2 * y + n) : ℚ)/ (n - 2)
            -- Prove that q is positive.
            have hqpos : q > 0 := by
              unfold q
              refine div_pos ?haa ?hbb
              · norm_cast
                linarith
              · norm_cast
                linarith
            -- Establish the relationship between q and n.
            have heqq : 4 * n + 1 = q ^ 2 := by unfold q; exact this
            have : ((4 * n + 1) : ℚ).den = 1 := by norm_cast
            have hq2 : (q ^ 2).den = q.den^2 := by norm_num
            rw [heqq, hq2] at this
            have : q.den = 1 := by exact Nat.eq_one_of_mul_eq_one_left this
            have : q = q.num := by exact Eq.symm ((fun r => (Rat.den_eq_one_iff r).mp) q this)
            rw [this] at hqpos
            norm_cast at hqpos
            rw [this] at heqq
            norm_cast at heqq
            -- Show that q is an odd integer.
            have : Odd ((q.num)^2) := by
              rw [← heqq]
              apply Even.add_odd
              · apply Even.mul_right
                exact Int.even_iff.mpr rfl
              · exact Int.odd_iff.mpr rfl
            have : Odd q.num := by exact Int.Odd.of_mul_right this
            rcases this with ⟨k, hm⟩
            -- Let q.num be expressed as 2k + 1.
            have hkpos : k ≥ 0 := by linarith
            rw [hm] at heqq
            -- Simplify the expression involving k.
            have : (2 * k + 1) ^ 2 = 4 * (k^2 + k) + 1 := by ring_nf
            rw [this] at heqq
            simp at heqq
            rw [heqq] at hyn
            -- Further simplify the equation.
            have : (k ^ 2 + k - 2) ^ 2 * (4 * (k ^ 2 + k) + 1) = ((k^2+k-2)*(2*k+1))^2 := by ring_nf
            rw [this] at hyn
            -- Prove that k is at least 2.
            have : k ≥ 2 := by
              rw [heqq] at hge3
              by_contra hk
              simp at hk
              have : k ≤ 1 := by exact Int.lt_add_one_iff.mp hk
              have : k ^ 2 ≤ 1 := by exact (sq_le_one_iff₀ hkpos).mpr this
              have : k ^ 2 + k ≤ 2 := by linarith
              linarith
            -- Prove non-negativity of expressions involving k and y.
            have hpos1 : 2 * y + (k ^ 2 + k) ≥ 0 := by
              have : k^2 + k ≥ 0 := by rw [← heqq]; linarith
              linarith
            have hpos2 : (k^2 + k - 2) * (2 * k + 1) ≥ 0 := by
              have h1 : k^2 + k - 2 ≥ 0 := by linarith
              have h2 : 2 * k + 1 ≥ 0 := by linarith
              exact Int.mul_nonneg h1 h2
            -- Equate the two expressions to solve for y.
            have hyk : 2 * y + (k ^ 2 + k) = (k ^ 2 + k - 2) * (2 * k + 1) := by
              apply (sq_eq_sq₀ hpos1 hpos2).mp hyn
            -- Express y in terms of k.
            have : 2 * y = 2 *(k ^ 3 + k ^ 2 - 2 * k - 1) := by
              calc
                _ = (2 * y + (k ^ 2 + k) - (k ^ 2 + k)) := by ring_nf
                _ = _ := by
                  rw [hyk]
                  ring_nf
            have : y = (k ^ 3 + k ^ 2 - 2 * k - 1) := by
              apply (Int.mul_eq_mul_left_iff (by linarith)).mp this
            -- Substitute back to find x in terms of k.
            rw [this, heqq] at heqadd
            ring_nf at heqadd
            -- Conclude the parametric solution.
            right
            use k
            constructor
            · linarith
            · constructor
              · rw [heqadd]
                ring_nf
              · rw [this]

