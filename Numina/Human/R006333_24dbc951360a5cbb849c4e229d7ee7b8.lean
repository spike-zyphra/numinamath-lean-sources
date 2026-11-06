import Mathlib

open Real Finset

lemma real_rpow_right_inj {x y z : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  have x_or : x < 1 ∨ x > 1 := by 
    by_cases hx : x < 1 
    left 
    exact hx
    simp at hx
    right 
    exact lt_of_le_of_ne hx (id (Ne.symm hx₁))
  obtain h | h := x_or
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

lemma pow_le_aux {n : ℕ} (hn : 0 < n) (h1 : ⌊logb 2 (n : ℝ)⌋₊ ≠ ⌊logb 2 ((n : ℝ) + 1) ⌋₊) : n + 1 ≤ 2 ^ (⌊logb 2 n⌋₊ + 1) := by
  have eq3 : n = 2 ^ ⌊logb 2 ((n : ℝ) + 1)⌋₊ - 1 := by 
    have aux : n + 1 = 2 ^ ⌊logb 2 ((n : ℝ) + 1)⌋₊ := by 
      have aux3 : (n : ℝ) + 1 = 2 ^ (logb 2 ((n : ℝ) + 1)) := by  
        refine Eq.symm (rpow_logb ?_ ?_ ?_)
        linarith
        linarith
        norm_cast
        linarith
      have aux4 : (n : ℝ) + 1 = 2 ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) := by 
        have aux5 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≤ logb 2 (↑n + 1) := by 
          refine Nat.floor_le ?_
          refine logb_nonneg ?_ ?_
          linarith
          norm_cast
          linarith
        have aux6 : (2 : ℝ) ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≤ 2 ^ (logb 2 (↑n + 1) ) := by 
          apply Real.rpow_le_rpow_of_exponent_le
          linarith
          exact aux5
        rw [←aux3] at aux6
        have aux7 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) > ↑⌊logb 2 (↑n)⌋₊ := by 
          have aux1 : ⌊logb 2 n⌋₊ ≤  ⌊logb 2 (↑n + 1)⌋₊ := by 
            have aux2 : logb 2 n ≤  logb 2 (↑n + 1) := by 
              refine logb_le_logb_of_le ?_ ?_ ?_
              linarith
              norm_cast
              linarith
            exact Nat.floor_le_floor aux2
          have aux2 : ⌊logb 2 n⌋₊ <  ⌊logb 2 (↑n + 1)⌋₊ := by 
            exact Nat.lt_of_le_of_ne aux1 h1
          norm_cast
          norm_num
          exact aux2
        have aux8 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) >  logb 2 n := by 
          have ineq : ⌊logb 2 n⌋₊ + 1 > logb 2 n := by 
            exact Nat.lt_floor_add_one (logb 2 ↑n)
          have aux7' : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≥ ⌊logb 2 ↑n⌋₊ + 1 := by 
            norm_cast at aux7 ⊢ 
          linarith
        have ineq1 : (2 : ℝ) ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) > 2 ^ (logb 2 n) := by 
          apply Real.rpow_lt_rpow_of_exponent_lt
          linarith
          norm_cast at aux8
          norm_num at aux8
          exact aux8
        have eq3 : (2 : ℝ) ^ logb 2 (n : ℝ) = n := by 
          refine rpow_logb ?_ ?_ ?_
          linarith
          linarith
          norm_cast
        rw [eq3] at ineq1
        norm_cast at ineq1
        norm_cast at aux6 ⊢
        linarith
      norm_cast at aux4
      norm_num at aux4
      exact aux4
    omega
  nth_rw 1 [eq3]
  have ineq : 2 ^ ⌊logb 2 (↑n + 1)⌋₊ ≥ 1 := by 
    exact Nat.one_le_two_pow
  have aux1 : 2 ^ ⌊logb 2 (↑n + 1)⌋₊ - 1 + 1 = 2 ^ ⌊logb 2 (↑n + 1)⌋₊ := by 
    omega
  rw [aux1]
  have aux2 : ⌊logb 2 (↑n + 1)⌋₊ ≤ (⌊logb 2 ↑n⌋₊ + 1) := by 
    have aux3 : ⌊logb 2 (↑n + 1)⌋₊ = logb 2 (↑n + 1) := by 
      have eq1 : (2 : ℝ) ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) = (2 : ℝ) ^ (logb 2 (n + 1)) := by 
        have eq2 : (2 : ℝ) ^ (logb 2 (n + 1)) = n + 1 := by 
          refine rpow_logb ?_ ?_ ?_
          linarith
          linarith
          norm_cast 
          linarith
        rw [eq2]
        nth_rw 2 [eq3]
        norm_num
      refine (real_rpow_right_inj ?_ ?_).mp eq1
      linarith
      linarith
    have ineq_aux : ⌊logb 2 (↑n + 1)⌋₊ - 1 ≤ ⌊logb 2 ↑n⌋₊ := by 
      by_cases hn1 : n = 1
      rw [hn1]
      simp
      norm_num
      by_cases hn2 : n = 2 
      simp [hn2]
      norm_num
      apply Nat.floor_le_of_le
      refine (logb_le_iff_le_rpow ?_ ?_).mpr ?_
      linarith
      linarith
      norm_num
      have nge3 : n ≥ 3 := by 
        omega
      refine (Nat.le_floor_iff' ?_).mpr ?_ 
      have ge_aux : ⌊logb 2 (↑n + 1)⌋₊ > 1 := by 
        have logb_ge : logb 2 (↑n + 1) ≥ 2 := by 
          have ge2 : (n : ℝ) + 1 ≥ 4 := by 
            norm_cast 
            linarith
          have aux : (2 : ℝ) = logb 2 4  := by 
            apply Eq.symm
            refine (logb_eq_iff_rpow_eq ?_ ?_ ?_ ).mpr ?_ 
            linarith
            linarith
            linarith
            linarith
          nth_rw 2 [aux]
          refine logb_le_logb_of_le ?_ ?_ ge2
          linarith
          linarith
        have ineq2 : ⌊logb 2 (↑n + 1)⌋₊ ≥ logb 2 (↑n + 1) := by 
          exact le_of_eq (id (Eq.symm aux3))
        have ineq3 : ⌊logb 2 (↑n + 1)⌋₊ > (1 : ℝ) := by 
          linarith
        norm_cast at ineq3
        norm_num at ineq3
        exact ineq3
      omega
      rw [Nat.cast_sub, aux3]
      have ineq1 : (2 : ℝ) ^ (logb 2 (↑n + 1) - 1) ≤ 2 ^ (logb 2 ↑n) := by 
        rw [rpow_sub]
        simp
        have eq1 : (2 : ℝ) ^ logb 2 (↑n + 1) = n + 1 := by 
          refine rpow_logb ?_ ?_ ?_
          linarith
          linarith
          norm_cast
          linarith
        have eq2 : (2 : ℝ) ^ logb 2 (↑n ) = n := by 
          refine rpow_logb ?_ ?_ ?_
          linarith
          linarith
          norm_cast
        rw [eq1, eq2]
        norm_num
        refine (div_le_iff₀ ?_).mpr ?_ 
        linarith
        have nge1 : n ≥ 1 := by exact hn
        norm_cast
        linarith
        linarith
      have gt1 : (2 : ℝ) > 1 := by norm_num
      obtain h2 := (rpow_le_rpow_left_iff gt1).mp ineq1
      norm_num
      norm_num at h2
      exact h2
      have ge1 : logb 2 (↑n + 1) ≥ 1 := by 
        refine (le_logb_iff_rpow_le ?_ ?_).mpr ?_
        linarith
        norm_cast
        linarith
        norm_cast
        linarith
      exact (Nat.one_le_floor_iff (logb 2 (↑n + 1))).mpr ge1
    omega
  apply pow_le_pow 
  linarith
  linarith
  exact aux2


theorem number_theory_635967 (N : ℕ) (hN : 0 < N) (M : ℕ) (hM : M = ⌊logb 2 N⌋₊) :
  ∑ i ∈ Finset.Icc 1 N, ⌊logb 2 i⌋ = (N + 1) * M - 2^(M + 1) + 2 := by 
  have h0 : ∀ (k : ℕ), k > 0 → ∑ i ∈ Icc 1 k, ⌊logb 2 ↑i⌋ = (↑k + 1) * ↑⌊logb 2 ↑k⌋₊ - 2 ^ (⌊logb 2 ↑k⌋₊ + 1) + 2 := by 
    -- use induction to prove the theorem, and discuss the jump point related to logarithm. 
    intro k hk
    induction' hk with n ih1 ih2
    · simp_all 
    · simp at ih1
      simp
      have seteq1 : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by 
        refine Eq.symm (Nat.Icc_insert_succ_right ?_)
        linarith
      rw [seteq1, sum_insert]
      by_cases h1 : ⌊logb 2 (n : ℝ)⌋₊ = ⌊logb 2 ((n : ℝ) + 1) ⌋₊
      · norm_num
        have eq1 : ⌊logb 2 (↑n + 1)⌋₊ = ⌊logb 2 (↑n + 1)⌋ := by 
          refine Int.natCast_floor_eq_floor ?_
          refine logb_nonneg ?_ ?_
          linarith
          linarith 
        rw [ih2, ←eq1, ←h1]
        ring
      · 
        have eq1 : ⌊logb 2 (↑n + 1)⌋₊ = ⌊logb 2 (↑n + 1)⌋ := by 
          refine Int.natCast_floor_eq_floor ?_
          refine logb_nonneg ?_ ?_
          linarith
          linarith 
        have eq2 : ⌊logb 2 ((n : ℝ) + 1)⌋₊ = ⌊logb 2 ((n : ℝ))⌋₊ + 1 := by 
          have aux1 : ⌊logb 2 n⌋₊ ≤  ⌊logb 2 (↑n + 1)⌋₊ := by 
            have aux2 : logb 2 n ≤  logb 2 (↑n + 1) := by 
              refine logb_le_logb_of_le ?_ ?_ ?_
              linarith
              norm_cast
              linarith
            exact Nat.floor_le_floor aux2
          have aux2 : ⌊logb 2 n⌋₊ <  ⌊logb 2 (↑n + 1)⌋₊ := by 
            exact Nat.lt_of_le_of_ne aux1 h1
          have aux3 : ⌊logb 2 n⌋₊ + 1 ≤ ⌊logb 2 (↑n + 1)⌋₊ := by 
            linarith
          have aux4 : ⌊logb 2 n⌋₊ + 1 ≥ ⌊logb 2 (↑n + 1)⌋₊ := by
            refine Nat.floor_le_of_le ?_
            refine (logb_le_iff_le_rpow ?_ ?_).mpr ?_
            linarith
            linarith
            have aux4 : n > 0 := by 
              linarith
            obtain h2 := pow_le_aux aux4 h1
            norm_cast
          linarith
        norm_num
        have eq3 : n = 2 ^ ⌊logb 2 ((n : ℝ) + 1)⌋₊ - 1 := by 
          have aux : n + 1 = 2 ^ ⌊logb 2 ((n : ℝ) + 1)⌋₊ := by 
            have aux3 : (n : ℝ) + 1 = 2 ^ (logb 2 ((n : ℝ) + 1)) := by  
              refine Eq.symm (rpow_logb ?_ ?_ ?_)
              linarith
              linarith
              norm_cast
              linarith
            have aux4 : (n : ℝ) + 1 = 2 ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) := by 
              have aux5 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≤ logb 2 (↑n + 1) := by 
                refine Nat.floor_le ?_
                refine logb_nonneg ?_ ?_
                linarith
                norm_cast
                linarith
              have aux6 : (2 : ℝ) ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≤ 2 ^ (logb 2 (↑n + 1) ) := by 
                apply Real.rpow_le_rpow_of_exponent_le
                linarith
                exact aux5
              rw [←aux3] at aux6
              have aux7 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) > ↑⌊logb 2 (↑n)⌋₊ := by 
                have aux1 : ⌊logb 2 n⌋₊ ≤  ⌊logb 2 (↑n + 1)⌋₊ := by 
                  have aux2 : logb 2 n ≤  logb 2 (↑n + 1) := by 
                    refine logb_le_logb_of_le ?_ ?_ ?_
                    linarith
                    norm_cast
                    linarith
                  exact Nat.floor_le_floor aux2
                have aux2 : ⌊logb 2 n⌋₊ <  ⌊logb 2 (↑n + 1)⌋₊ := by 
                  exact Nat.lt_of_le_of_ne aux1 h1
                norm_cast
                norm_num
                exact aux2
              have aux8 : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) >  logb 2 n := by 
                have ineq : ⌊logb 2 n⌋₊ + 1 > logb 2 n := by 
                  exact Nat.lt_floor_add_one (logb 2 ↑n)
                have aux7' : (⌊logb 2 (↑n + 1)⌋₊ : ℝ) ≥ ⌊logb 2 ↑n⌋₊ + 1 := by 
                  norm_cast at aux7 ⊢ 
                linarith
              have ineq1 : (2 : ℝ) ^ (⌊logb 2 (↑n + 1)⌋₊ : ℝ) > 2 ^ (logb 2 n) := by 
                apply Real.rpow_lt_rpow_of_exponent_lt
                linarith
                norm_cast at aux8
                norm_num at aux8
                exact aux8
              have eq3 : (2 : ℝ) ^ logb 2 (n : ℝ) = n := by 
                refine rpow_logb ?_ ?_ ?_
                linarith
                linarith
                norm_cast
              rw [eq3] at ineq1
              norm_cast at ineq1
              norm_cast at aux6 ⊢
              linarith
            norm_cast at aux4
            rw [aux4]
            norm_num
          omega
        rw [←eq1,eq2, ih2]
        nth_rw 2 5 [eq3]
        norm_num
        rw [eq2]
        ring_nf
      simp
  obtain h1 := h0 N hN
  rw [←hM] at h1
  exact h1
