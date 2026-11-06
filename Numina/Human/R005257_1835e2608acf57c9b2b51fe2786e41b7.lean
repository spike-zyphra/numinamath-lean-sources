import Mathlib

/- Trouver la somme des $n$ tels que $n^{2}+8 n+44$ soit un carré parfait. -/
theorem algebra_607209 (n : ℕ) : ∑ᶠ n ∈ {n : ℤ | IsSquare (n ^ 2 + 8 * n + 44)}, n = -8 := by
  have h₁ : ∀ (n : ℤ), IsSquare (n ^ 2 + 8 * n + 44) ↔ n = 2 ∨ n = -10 := by
    intro n
    rw [IsSquare]
    apply Iff.intro
    . rintro ⟨r, hr⟩
      rw [<-pow_two] at hr
      replace hr : 28 + (n + 4) ^ 2 = r ^ 2 := by
        linarith only [hr]
      apply eq_sub_of_add_eq at hr
      rw [sq_sub_sq] at hr
      -- We have (r + (n + 4)) * (r - (n + 4)) = 28.
      let x : ℕ × ℕ := ((r + (n + 4)).natAbs, (r - (n + 4)).natAbs)
      have hx : x.1 * x.2 = 28 ∧ 28 ≠ 0 := by
        refine ⟨?_, ?_⟩
        . simp [x, <-Int.natAbs_mul, <-hr]
        . norm_num
      rw [<-Nat.mem_divisorsAntidiagonal] at hx
      -- Use the computer to find the factors of 28 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 28 = {(1, 28), (2, 14), (4, 7), (7, 4), (14, 2), (28, 1)} by native_decide] at hx
      -- We need both factors to have the same parity.
      have hx' : ¬((Even x.1 ∧ Odd x.2) ∨ (Odd x.1 ∧ Even x.2)) := by
        -- Proof by contradiction.
        by_contra hx'
        simp [-not_and] at hx'
        cases hx' with
        | inl hx' =>
          -- If r + (n + 4) is even but r - (n + 4) is odd, then 2 * r is odd.
          have hx'' : Odd (2 * r) := by
            rw [show 2 * r = r + (n + 4) + (r - (n + 4)) by ring]
            apply Even.add_odd hx'.1 hx'.2
          -- But 2 * r is even, contradiction.
          exact absurd hx'' (by norm_num)
        | inr hx' =>
          -- If r + (n + 4) is odd but r - (n + 4) is even, then 2 * r is odd.
          have hx'' : Odd (2 * r) := by
            rw [show 2 * r = r + (n + 4) + (r - (n + 4)) by ring]
            apply Odd.add_even hx'.1 hx'.2
          -- But 2 * r is even, contradiction.
          exact absurd hx'' (by norm_num)
      -- We can eliminate the case where one of the factors is odd but the other is even.
      simp at hx
      rcases hx with (hx | hx | hx | hx | hx | hx)
      all_goals
        rw [hx] at hx'
        norm_num at hx'
        norm_cast at hx'
      clear hx'
      -- Remaining two cases: (r + (n + 4), r - (n + 4)) = (2, 14) or (14, 2).
      . -- Consider cases 0 ≤ r + (n + 4) and r + (n + 4) < 0.
        have hr'' := (show (0 : ℤ) ≤ 28 by norm_num).trans_eq hr
        cases le_or_lt 0 (r + (n + 4)) with
        | inl hr' =>
          rw [le_iff_lt_or_eq] at hr'
          cases hr' with
          | inl hr' =>
            rw [mul_comm, Int.mul_nonneg_iff_of_pos_right hr'] at hr''
            -- Now 0 ≤ r + (n + 4), r - (n + 4).
            have hr₁ : r + (n + 4) = 2 := by
              rw [show (2 : ℤ) = x.1 by rw [hx]; norm_num]
              simp [x, abs_of_nonneg (le_of_lt hr')]
            have hr₂ : r - (n + 4) = 14 := by
              rw [show (14 : ℤ) = x.2 by rw [hx]; norm_num]
              simp [x, abs_of_nonneg hr'']
            -- Subtracting the two equations, we get n = -10.
            omega
          | inr hr' =>
            -- It is impossible that 0 = r + (n + 4), because the product of x.1 and x.2 is 28 > 0.
            simp [<-hr'] at hr
        | inr hr' =>
          -- Now r + (n + 4) < 0, so r - (n + 4) ≤ 0.
          rw [mul_comm] at hr''
          apply nonpos_of_mul_nonneg_left at hr''
          simp only [hr', true_implies] at hr''
          have hr₁ : r + (n + 4) = -2 := by
            rw [show (-2 : ℤ) = -x.1 by rw [hx]; norm_num]
            simp [x, abs_of_neg hr']
          have hr₂ : r - (n + 4) = -14 := by
            rw [show (-14 : ℤ) = -x.2 by rw [hx]; norm_num]
            simp [x, abs_of_nonpos hr'']
          -- Subtracting the two equations, we get n = 2.
          omega
      . -- Consider cases 0 ≤ r + (n + 4) and r + (n + 4) < 0.
        have hr'' := (show (0 : ℤ) ≤ 28 by norm_num).trans_eq hr
        cases le_or_lt 0 (r + (n + 4)) with
        | inl hr' =>
          rw [le_iff_lt_or_eq] at hr'
          cases hr' with
          | inl hr' =>
            rw [mul_comm, Int.mul_nonneg_iff_of_pos_right hr'] at hr''
            -- Now 0 ≤ r + (n + 4), r - (n + 4).
            have hr₁ : r + (n + 4) = 14 := by
              rw [show (14 : ℤ) = x.1 by rw [hx]; norm_num]
              simp [x, abs_of_nonneg (le_of_lt hr')]
            have hr₂ : r - (n + 4) = 2 := by
              rw [show (2 : ℤ) = x.2 by rw [hx]; norm_num]
              simp [x, abs_of_nonneg hr'']
            -- Subtracting the two equations, we get n = 2.
            omega
          | inr hr' =>
            -- It is impossible that 0 = r + (n + 4), because the product of x.1 and x.2 is 28 > 0.
            simp [<-hr'] at hr
        | inr hr' =>
          -- Now r + (n + 4) < 0, so r - (n + 4) ≤ 0.
          rw [mul_comm] at hr''
          apply nonpos_of_mul_nonneg_left at hr''
          simp only [hr', true_implies] at hr''
          have hr₁ : r + (n + 4) = -14 := by
            rw [show (-14 : ℤ) = -x.1 by rw [hx]; norm_num]
            simp [x, abs_of_neg hr']
          have hr₂ : r - (n + 4) = -2 := by
            rw [show (-2 : ℤ) = -x.2 by rw [hx]; norm_num]
            simp [x, abs_of_nonpos hr'']
          -- Subtracting the two equations, we get n = -10.
          omega
    . rintro (hn | hn)
      . rw [hn]
        use 8
        ring
      . rw [hn]
        use 8
        ring
  have h₂ : {n : ℤ | IsSquare (n ^ 2 + 8 * n + 44)} = {2, -10} := by
    ext n
    simp [Set.mem_setOf, h₁]
  rw [h₂, finsum_mem_pair]
  norm_num
  norm_num
