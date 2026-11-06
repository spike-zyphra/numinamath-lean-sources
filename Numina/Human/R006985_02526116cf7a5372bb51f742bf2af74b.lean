import Mathlib

open Real

/- 55. (USS 2) Find all $x$ for which for all $n$,  $$ \sin x+\sin 2 x+\sin 3 x+\cdots+\sin n x \leq \frac{\sqrt{3}}{2} $$ -/
theorem other_24737 (x : ℝ) :
    (∀ n : ℕ, ∑ k in Finset.Icc 1 n, sin (k * x) ≤ sqrt 3 / 2) ↔ (∃ k : ℤ, 2 * π / 3 + 2 * k * π ≤ x ∧ x ≤ 2 * (k + 1) * π) := by
  -- Using alternative solution given in https://math.stackexchange.com/a/4882748.
  -- First simplify the summation of sin kx.
  have h₀ (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 2 * π) : ∑ k in Finset.Icc 1 n, sin (k * x) = sin ((n + 1) * (x / 2)) * sin (n * (x / 2)) / sin (x / 2) := by
    let y : ℝ := x / 2
    nth_rewrite 1 [show x = x / 2 * 2 by simp]
    rw [show x / 2 = y by dsimp [y]]
    have h₀ : sin y ≠ 0 := by
      rw [sin_ne_zero_iff]
      intro n
      by_contra! g
      simp [y] at g
      field_simp at g
      rw [<-g] at hx
      nth_rewrite 2 [mul_assoc] at hx
      nth_rewrite 4 [mul_comm] at hx
      simp [pi_pos] at hx
      norm_cast at hx
      omega
    -- Use induction on n.
    induction n with
    | zero =>
      simp
    | succ n hn =>
      rw [Finset.sum_Icc_succ_top (by omega), hn]
      apply @Or.resolve_right _ (sin y = 0) _ (by apply h₀)
      rw [<-mul_eq_mul_right_iff, add_mul, div_mul_cancel₀]
      nth_rewrite 2 [div_mul_cancel₀]
      rw [add_comm]
      apply add_eq_of_eq_sub
      nth_rewrite 2 [mul_comm]
      nth_rewrite 3 [mul_comm]
      rw [mul_assoc, sin_two_mul]
      nth_rewrite 6 [mul_comm]
      simp
      rw [<-mul_sub, sin_sub_sin]
      ring_nf
      all_goals
        exact h₀
  -- Show that ∑sin kx ≤ √3/2 ↔ cos(x / 2 + π / 3) ≤ cos((2n + 1)(x / 2)) / 2.
  have h₁ (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 2 * π) : (∑ k in Finset.Icc 1 n, sin (k * x) ≤ sqrt 3 / 2) ↔ cos (x / 2 + π / 3) ≤ cos ((2 * n + 1) * (x / 2)) / 2 := by
    rw [h₀ _ _ hx]
    conv =>
      rhs
      rw [cos_add, cos_pi_div_three, sin_pi_div_three]
      rw [sub_le_comm, div_eq_mul_one_div (cos ((2 * n + 1) * (x / 2))) 2, <-sub_mul, Real.cos_sub_cos, neg_mul, neg_mul, mul_assoc, mul_comm (sin ((x / 2 + (2 * n + 1) * (x / 2)) / 2)) (sin ((x / 2 - (2 * n + 1) * (x / 2)) / 2)), <-mul_neg, <-neg_mul, <-sin_neg]
    apply Iff.intro
    all_goals
      intro h
      ring_nf at h ⊢
      field_simp at h ⊢
      try rw [div_le_iff₀] at h
      try rw [div_le_iff₀]
      linarith
      apply Real.sin_pos_of_mem_Ioo
      simp
      refine ⟨by linarith only [hx], by linarith only [hx]⟩
  -- Break the iff into two implications.
  apply Iff.intro
  <;> intro h₂
  . let m : ℤ := ⌊x / (2 * π)⌋
    by_cases h₃ : x = 2 * π * m
    . -- If x is integral multiple of 2π.
      use m - 1
      conv =>
        congr
        . rw [h₃, mul_comm, mul_div_assoc, mul_comm, <-add_mul, mul_assoc, mul_comm]
        . norm_cast
          rw [h₃, mul_comm, <-mul_assoc]
      simp [pi_pos]
      refine ⟨by linarith, by linarith⟩
    . -- If x is not an integral multiple of 2π.
      use m
      have h₃' := h₃
      have h₃ : m ≤ x / (2 * π) ∧ x / (2 * π) < m + 1 := by
        simp [m, Int.floor_le]
      obtain ⟨h₃, h₄⟩ := h₃
      replace h₃ : 2 * m * π < x := by
        rw [le_div_iff₀] at h₃
        ring_nf at h₃ ⊢
        rw [<-ne_eq] at h₃'
        ring_nf at h₃ h₃' ⊢
        exact lt_of_le_of_ne h₃ h₃'.symm
        positivity
      clear h₃'
      replace h₄ : x < 2 * (m + 1) * π := by
        rw [div_lt_iff] at h₄
        exact h₄.trans_eq (by ac_rfl)
        positivity
      refine ⟨?_, by apply le_of_lt; exact h₄⟩
      conv at h₂ =>
        intro n
        lhs
        congr
        . skip
        . ext k
          rw [<-Real.sin_sub_int_mul_two_pi _ (k * m)]
          simp
          rw [mul_assoc, <-mul_sub, show m * (2 * π) = 2 * m * π by ac_rfl]
      -- We shall prove that x - 2mπ ≥ 2π / 3 by contradiction if otherwise.
      by_contra! h₅
      -- Let n be the lartest integer such that n(x - 2mπ) ≤ 2π / 3.
      let n : ℤ := ⌊2 * π / 3 / (x - 2 * m * π)⌋
      have hn₁ : 1 ≤ n := by
        simp [n]
        rw [Int.le_floor]
        rw [le_div_iff₀]
        simp
        linarith only [h₅]
        linarith only [h₃]
      have hn₂ : n ≤ 2 * π / 3 / (x - 2 * m * π) := by
        simp [n]
        apply Int.floor_le
      have hn₃ : 2 * π / 3 / (x - 2 * m * π) < 2 * n := by
        calc
          2 * π / 3 / (x - 2 * m * π) < n + 1 := by simp [n]
          _ ≤ 2 * n := by norm_cast; linarith only [hn₁]
      replace hn₂ : n * (x - 2 * m * π) ≤ 2 * π / 3 := by
        rw [le_div_iff₀] at hn₂
        exact hn₂
        linarith only [h₃]
      replace hn₃ : π / 3 < n * (x - 2 * m * π) := by
        rw [div_lt_iff, mul_div_assoc, mul_assoc] at hn₃
        simp at hn₃
        exact hn₃
        linarith only [h₃]
      -- Use n at h₂ and show that it is not true.
      specialize h₂ n.natAbs
      absurd h₂
      by_cases h₆ : n = 1
      . -- Just the term sin x is already greater than √3 / 2.
        simp [h₆]
        rw [<-sin_pi_div_three]
        by_cases h₇ : x - 2 * m * π ≥ π / 2
        . nth_rewrite 2 [<-sin_pi_sub]
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          linarith only [pi_pos]
          linarith only [h₇]
          rw [h₆] at hn₂
          simp at hn₂
          apply lt_of_le_of_ne
          . linarith only [hn₂]
          . linarith only [h₅]
        . simp at h₇
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          linarith only [pi_pos]
          apply le_of_lt h₇
          rw [h₆] at hn₃
          simp at hn₃
          exact hn₃
      . -- Just the term sin nx is already greater than or equal to √3 / 2.
        simp
        calc
          Real.sqrt 3 / 2 ≤ sin (n.natAbs * (x - 2 * m * π)) := by
            have g (m : ℕ) : (m : ℝ) = (m : ℤ) := by
              simp
            rw [g n.natAbs, Int.natAbs_of_nonneg, <-sin_pi_div_three]
            by_cases h₇ : n * (x - 2 * m * π) ≥ π / 2
            . nth_rewrite 2 [<-sin_pi_sub]
              apply Real.sin_le_sin_of_le_of_le_pi_div_two
              linarith only [pi_pos]
              linarith only [h₇]
              linarith only [hn₂]
            . apply Real.sin_le_sin_of_le_of_le_pi_div_two
              linarith only [pi_pos]
              simp at h₇
              apply le_of_lt h₇
              apply le_of_lt hn₃
            omega
          _ < sin (x - 2 * m * π) + sin (n.natAbs * (x - 2 * m * π)) := by
            simp
            apply Real.sin_pos_of_pos_of_lt_pi
            linarith only [h₃]
            calc
              x - 2 * m * π = 1 * (x - 2 * m * π) := by simp
              _ ≤ n * (x - 2 * m * π) := by rw [mul_le_mul_right]; norm_cast; linarith only [h₃]
              _ ≤ 2 * π / 3 := hn₂
              _ < π := by linarith only [pi_pos]
          _ = ∑ k ∈ {1} ∪ {n.natAbs}, sin (k * (x - 2 * m * π)) := by
            rw [Finset.sum_union]
            simp
            simp
            zify
            simp [abs, show n ≥ 0 by omega]
            exact h₆
          _ = ∑ k ∈ {1, n.natAbs}, sin (k * (x - 2 * m * π)) := by
            congr
          _ ≤ ∑ k ∈ Finset.Icc 1 n.natAbs, sin (k * (x - 2 * m * π)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            simp [Subset]
            zify
            simp [abs, show n ≥ 0 by omega]
            exact hn₁
            simp
            intro k hk₁ hk₂ _ _
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            apply mul_nonneg
            positivity
            linarith only [h₃]
            calc
              k * (x - 2 * m * π) ≤ n * (x - 2 * m * π) := by
                simp [show x - 2 * m * π > 0 by linarith only [h₃]]
                zify at hk₂
                simp [abs, show 0 ≤ n by positivity] at hk₂
                norm_cast
              _ ≤ 2 * π / 3 := by exact hn₂
              _ ≤ π := by linarith only [pi_pos]
  . obtain ⟨m, h₂, h₃⟩ := h₂
    intro n
    -- Replace sin kx by sin (k * (x - 2 * m * π)).
    conv =>
      lhs
      congr
      . skip
      . ext k
        rw [<-Real.sin_sub_int_mul_two_pi _ (k * m)]
        simp
        rw [mul_assoc, <-mul_sub]
    by_cases h₄ : x = 2 * π * (m + 1)
    . -- If x is an integral multiple of 2π.
      rw [h₄]
      conv =>
        lhs
        congr
        . skip
        . ext k
          ring_nf
          rw [show k * π * 2 = k * (2 * π) by ac_rfl, <-zero_add (k * (2 * π)), Real.sin_add_nat_mul_two_pi]
      simp
      positivity
    . -- If x is not an integral multiple of 2π.
      have h₂' := (show 2 * m * π < 2 * π / 3 + 2 * m * π by linarith [pi_pos]).trans_le h₂
      rw [<-ne_eq] at h₄
      ring_nf at h₃ h₄
      replace h₄ := lt_of_le_of_ne h₃ h₄
      rw [h₁ _ _ ⟨by linarith only [h₂'], by linarith only [h₄]⟩]
      cancel_denoms
      let y : ℝ := x - m * 2 * π
      -- We have cos (y / 2 + π / 3) ≤ -1 / 2, hence cos (y / 2 + π / 3) ≤ cos ((2n + 1)(y / 2)) / 2 for any n.
      refine le_trans ?_ (show -1 ≤ cos ((2 * n + 1) * (y / 2)) by apply Real.neg_one_le_cos)
      rw [show x - m * 2 * π = y by dsimp [y]]
      suffices h₅ : cos (y / 2 + π / 3) + cos (π / 3) ≤ 0 by
        rw [cos_pi_div_three] at h₅
        linarith only [h₅]
      rw [cos_add_cos, mul_assoc]
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      apply mul_nonpos_of_nonpos_of_nonneg
      . apply Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      . apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
      
