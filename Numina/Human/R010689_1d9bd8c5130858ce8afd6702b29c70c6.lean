import Mathlib

/- How many pairs of positive integers $(a, b)$ satisfy the equation
$$
\frac{1}{a}+\frac{1}{b}=\frac{1}{2014} ?
$$ -/
theorem number_theory_607517:
    {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 1 / 2014}.encard = 27 := by

    -- we will prove by constructing bijection f between sets
    let f: ℤ × ℤ → ℤ := fun (a, b) => (a - 2014)
    set s:= {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 1 / 2014} with hs

    -- prove the injectivity of f
    have hf: Set.InjOn f s := by
      intro ⟨a,b⟩
      intro l
      intro ⟨c,d⟩
      intro r
      intro h
      simp [f] at h
      simp [h]
      simp [s] at l r
      rcases l with ⟨l1,l2,l⟩
      rcases r with ⟨r1,r2,r⟩
      rw [h] at l
      rw [← r] at l
      simp at l
      exact l
    -- use the fact the cardinality of the image of a set under an injective function is equal to the cardinality of the set
    have card_eq:= Set.InjOn.encard_image hf
    let t: Set ℤ:= (Nat.divisors (2014 ^ 2)).image (fun n : ℕ => (n : ℤ))  -- turn the set of divisors of 2014^2 into a set of integers

    -- compute the image of f
    have f_image: f '' s = t := by
      ext n
      simp [s,t]
      constructor
      -- the forward direction
      . intro h
        obtain ⟨a, b, h⟩ := h
        rcases h with ⟨h1,h2⟩
        rcases h1 with ⟨ha,hb,h⟩
        simp [f] at h2
        have la: 2014 < a := by
          by_contra! la
          qify at la ha
          replace la: 2014⁻¹ ≤ (a: ℚ)⁻¹ := by
            field_simp
            apply div_le_div_of_nonneg_left
            norm_num
            exact ha
            exact la
          rw [← h] at la
          absurd la
          simp
          exact hb
        replace la: 0 < n := by omega
        use n.natAbs
        simp
        field_simp at h
        have eq: ((a: ℚ) - 2014) * ((b: ℚ) - 2014) = 2014 ^ 2 := by
          ring_nf
          rw [← h]
          ring_nf
        norm_cast at eq
        rw [h2] at eq
        rw [show ((2014 ^ 2: ℕ): ℤ) = (2014: ℤ) ^ 2 by simp] at eq
        have d: n ∣ 2014 ^ 2 := by
          rw [← eq]
          apply Int.dvd_mul_right
        constructor
        . rw [show (4056196: ℕ) = (4056196: ℤ).natAbs by simp]
          rw [Int.natAbs_dvd_natAbs]
          rw [show 2014 ^ 2 = (4056196: ℤ) by norm_num] at d
          exact d
        . omega
      -- the backward direction
      . intro h
        obtain ⟨x, h⟩ := h
        rcases h with ⟨d,hx⟩
        use n + 2014
        use 4056196 / n + 2014
        constructor
        . constructor
          . omega
          . constructor
            . have l: 0 < n := by
                rw [← hx]
                by_contra! no
                simp at no
                rw [no] at d
                tauto
              have o: 0 < 4056196 / n := by
                apply Int.ediv_pos_of_pos_of_dvd
                norm_num
                omega
                rw [← hx]
                zify at d
                exact d
              omega
            . have ne1: (n: ℚ) ≠ 0 := by
                by_contra! no
                simp at no
                rw [no] at hx
                simp at hx
                rw [hx] at d
                tauto
              have ne2: ((n + 2014): ℚ) ≠ 0 := by
                rw [show (n: ℚ) + 2014 = ↑(n + (2014: ℤ)) by simp]
                by_contra! no
                rw [show (0: ℚ) = ↑(0: ℤ) by simp] at no
                rw [Rat.intCast_inj] at no
                omega
              have ne3: ↑(4056196 / n) + (2014: ℚ) ≠ 0 := by
                have o: 0 < 4056196 / n := by
                  apply Int.ediv_pos_of_pos_of_dvd
                  norm_num
                  omega
                  rw [← hx]
                  zify at d
                  exact d
                qify at o
                nlinarith
              field_simp
              have o: ↑(4056196 / n) = 4056196 / (n: ℚ) := by
                 rw [Rat.intCast_div]
                 simp
                 rw [← hx]
                 qify at d
                 exact d
              rw [o]
              field_simp
              ring_nf
        . simp [f]

   -- Finally, combine the results to show that the cardinality of s is equal to the cardinality of t
    rw [hs,← card_eq,f_image]
    simp [t]
    rw [Function.Injective.encard_image]
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
    intro n m h
    simp at h
    exact h
    