import Mathlib

/- Find the positive integer $k$ for which the coefficient of $x^k$ in the expansion of $(x + 3)^{50}$ is maximized. -/
theorem algebra_21582 {k:ℕ} (kpos: 0 < k):
  (IsGreatest {m:ℕ | ∃k':ℕ, m = Polynomial.coeff ((Polynomial.X + 3)^50) k'}
  (Polynomial.coeff ((Polynomial.X + 3)^50) k)) ↔ k = 12 := by
  -- by binomial theorem, coefficient of x^k in expansion of (x+3)^50 is C 50^k 3^(50-k)
  have coeff_def'(k':ℕ): Polynomial.coeff ((Polynomial.X + 3)^50) k' =
    (Nat.choose 50 k') * 3^(50-k') := by
    have: Polynomial.X + 3 = Polynomial.X + Polynomial.C 3 := by simp
    rw [this]
    rw [Polynomial.coeff_X_add_C_pow]
    simp; ring
  -- let c denote coefficient of x^k in expansion of (x+3)^50
  let c : ℕ → ℕ := fun k => (Nat.choose 50 k) * 3^(50-k)
  have c_def: c = fun k => (Nat.choose 50 k) * 3^(50-k) := rfl
  have coeff_def(k':ℕ): Polynomial.coeff ((Polynomial.X+3)^50) k' = c k' := by
    rw [coeff_def', c_def]
  -- we can prove c reach maximum at k=12. to show that, we study ratio of each c k'.
  have h1(k':ℕ)(hk1: k' > 0)(hk2: k' < 50): c (k'+1) = (50-k')/(3*(k'+1):ℚ) * c k' := by
    rw [c_def]; simp
    have hh1: Nat.choose 50 (k'+1) = (Nat.choose 50 k') * (50-k':ℚ)/(k'+1)
      := by
      have tt1 := Nat.choose_succ_right_eq 50 k'
      have tt2: Nat.choose 50 (k'+1) = ↑((Nat.choose 50 (k'+1)) *(k'+1))/(k'+1:ℚ) := by
        have: (k'+1:ℚ) ≠ 0 := by
          exact Nat.cast_add_one_ne_zero k'
        field_simp [this]
      rw [tt2, tt1]
      simp [le_of_lt hk2]
    have hh2: (3:ℚ)^(50-k') = 3*(3:ℚ)^(49-k') := by
      have: 50-k' = 1 + (49-k') := by
        have tt1: k' ≤ 49 := Nat.le_of_lt_succ hk2
        have tt2: 50 = 1+49 := by norm_num
        rw [tt2]
        exact Nat.add_sub_assoc tt1 1
      rw [this]; ring
    rw [hh1, hh2]
    field_simp; ring
  -- ratio is (50-k'/(3(k'+1))), solve the equation 50-k' / 3(k'+1) ≥ 1, we get k' ≤ 11
  have h2(k':ℕ)(hk1: 0 < k')(hk2: k' < 50): (50-k':ℚ)/(3*(k'+1)) > 1 ↔ k' ≤ 11 := by
    have hh1: (50-k':ℚ)/(3*(k'+1)) > 1 ↔ (50-k':ℚ) > 3*(k'+1) := by
      have: (50-k':ℚ) = (50-k')/(3*(k'+1)) * (3*(k'+1)) := by
        field_simp [hk1, hk2]
      have tt1: 0 < (50-k':ℚ) := by
        simp [hk2]
      have tt2: 0 < (k':ℚ) := Nat.cast_pos.mpr hk1
      constructor <;> intro h
      · rw [← one_mul (3*(k'+1:ℚ))]
        rw [this]
        apply mul_lt_mul h (le_refl _)
        · linarith [tt2]
        · apply le_of_lt
          apply div_pos
          · linarith [tt1]
          · linarith [tt2]
      · have: 0 < 3*(k'+1:ℚ) := by linarith [tt2]
        apply (one_lt_div this).mpr h
    have hh2: (50-k':ℚ) > 3*(k'+1) ↔ (k':ℚ) < 47/4 := by
      constructor <;> intro h
      · linarith [h]
      · linarith [h]
    -- k ≤ 47/4, so k < 12, k ≤ 11
    rw [hh1, hh2]
    constructor <;> intro h
    · have tt1: (k':ℚ) < 12 := by linarith [h]
      have tt2: k' < 12 := Nat.cast_lt.mp tt1
      exact Nat.le_of_lt_succ tt2
    · have: (k':ℚ) ≤ 11 := Nat.cast_le.mpr h
      linarith [this]
  have h2'(k':ℕ): k' ≥ 12 →
    (50-k':ℚ)/(3*(k'+1)) < 1 := by
    intro hk
    have hk1': k' ≥ (12:ℚ) := by
      apply Nat.cast_le.mpr hk
    have hh1: (50-k':ℚ) < (3*(k'+1)) := by
      have tt1: (50:ℚ) < 3*(k'+1)+k' := by linarith [hk1']
      apply sub_right_lt_of_lt_add tt1
    refine (div_lt_iff' ?_).mpr ?_
    linarith [hk1']
    linarith [hh1]
  -- obviously, all c-terms are positive.
  have cpos(k':ℕ)(hk: k' < 50): 0 < (c k': ℚ) := by
    have: 0 < c k' := by
      rw [← coeff_def, coeff_def']
      apply mul_pos
      · apply Nat.choose_pos (le_of_lt hk)
      · simp
    apply Nat.cast_pos.mpr this
  -- when k ≤ 12, c k is increasing
  have h3(k':ℕ)(hk1: 0 < k')(hk2: k' ≤ 11): c k' < c (k'+1) := by
    have: (c k':ℚ) < (c (k'+1) : ℚ) := by
      rw [← one_mul (c k':ℚ)]
      rw [h1 k' hk1 (by linarith [hk2])]
      have := (h2 k' hk1 (by linarith [hk2])).mpr hk2
      apply mul_lt_mul_of_pos_right this (cpos k' (by linarith [hk2]))
    apply Nat.cast_lt.mp this
  -- and when k ≥ 12, c k is decreasing
  have h4(k':ℕ)(hk1: k' ≥ 12)(hk2: k' < 50): c k' > c (k'+1) := by
    have: (c k':ℚ) > c (k'+1) := by
      rw [← one_mul (c k':ℚ)]
      rw [h1 k' (by linarith [hk1]) hk2]
      apply mul_lt_mul_of_pos_right ?_ (cpos k' hk2)
      apply h2' k' hk1
    apply Nat.cast_lt.mp this
  -- thus 12 is the maximum
  have h5: ∀k':ℕ, 0 ≤ k' → k' ≤ 50 → c 12 > c k' ∨ k' = 12 := by
    intro k' _ hk2
    by_cases hk: k' ≤ 12
    · have hh1: ∀a:ℕ, a ≤ 12 → c 12 > c (12-a) ∨ a = 0 := by
        intro a ale'
        induction' a with d hd
        · simp
        · left
          rcases (hd (by linarith [ale'])) with hh | hh
          apply lt_trans ?_ hh
          have tt1: 12-d = 12-(d+1)+1 := by omega
          rw [tt1]
          by_cases hale: d+1 = 12; rw [hale, c_def]; simp
          have ale: d+1 ≤ 11 := by omega
          apply h3 _ (by omega) (by omega)
          rw [hh]; simp; apply h3 11 (by norm_num) (le_refl _)
      have hh2: k' = 12 - (12-k') := by
        exact Eq.symm (Nat.sub_sub_self hk)
      rw [hh2]
      have := hh1 (12-k') (by simp)
      rcases this with hh | hh
      · left; exact hh
      · right; rw [hh]
    · push_neg at hk
      have hh1: ∀a:ℕ, a+12 ≤ 50 → c 12 > c (a+12) ∨ a = 0 := by
        intro a ha
        induction' a with d hd
        · simp
        · have tt1: d+12 ≤ 50 := by omega
          left
          rcases (hd tt1) with hh | hh
          · apply lt_trans ?_ hh
            have tt2: d+1+12 = (d+12)+1 := by norm_num
            have tt3: (d+12) < 50 := by
              rw [tt2] at ha
              exact ha
            rw [tt2]
            apply h4 (d+12) (by simp) tt3
          · rw [hh]; simp
            apply h4 12 (by simp) (by norm_num)
      have hh2: k' = (k'-12)+12 := by omega
      rw [hh2]
      rcases (hh1 (k'-12) (by simp [hk2])) with hh | hh
      · left; exact hh
      · rw [hh]; simp
  -- thus we can solve the problem
  rw [IsGreatest, upperBounds]; simp
  constructor <;> intro h
  · -- from c k max, prove k=12
    -- k must ≤ 50, otherwise coefficient is 0, obviously not maximum
    have h6: k ≤ 50 := by
      by_contra! kgt
      have hh1: Polynomial.coeff ((Polynomial.X+3)^50) k = 0 := by
        rw [coeff_def']
        have: Nat.choose 50 k = 0 := by
          exact Nat.choose_eq_zero_iff.mpr kgt
        simp [this]
      have hh2: 3^50 ≤ 0 := by
        have: Polynomial.coeff ((Polynomial.X+3)^50) 0 = 3^50 := by
          rw [coeff_def']; simp
        rw [← hh1, ← this]
        apply h
      norm_num at hh2
    rcases (h5 k (le_of_lt kpos) h6) with hgt | heq
    · have: c 12 ≤ c k := by
        rw [← coeff_def, ← coeff_def]
        apply h
      linarith [hgt, this]
    · exact heq
  · -- given k=12, prove c k max.
    intro m
    by_cases hm: m > 50
    · rw [coeff_def]
      have: c m = 0 := by
        rw [← coeff_def, coeff_def']
        simp
        exact Nat.choose_eq_zero_iff.mpr hm
      rw [this]; simp
    · push_neg at hm
      rcases (h5 m (by simp) hm) with hh | hh
      · rw [coeff_def, coeff_def, h]
        apply le_of_lt hh
      · rw [hh, h]