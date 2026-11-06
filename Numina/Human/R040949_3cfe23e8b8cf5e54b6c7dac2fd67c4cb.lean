import Mathlib

/- B4. Solve the equation: $\log \left(4+2^{x+2}\right)=\log 4+\log \left(5 \cdot 2^{4-x}-1\right)$. -/
theorem algebra_146482 (x : ℝ) :
    Real.log (4 + 2^(x + 2)) = Real.log 4 + Real.log (5 * 2^(4 - x) - 1) ↔ x = 3 := by

      have pow_sub_x : (2 : ℝ) ^ (4 - x) = ((2 : ℝ) ^ (4 : ℝ) / 2 ^ x) := by
        rw [Real.rpow_sub]
        linarith only
      constructor
      · intro aa
        by_cases hx : x = 0
        -- if x = 0, we get log 8 = log 316
        · subst hx
          rw [←Real.log_mul] at aa
          ring_nf at aa
          -- log is injective on positive numbers, so 8 = 316
          have log_inj := Real.log_injOn_pos ?_ ?_ aa
          -- contradiction
          linarith only [log_inj]

          -- 8 is positive
          · simp only [Set.mem_Ioi, Nat.ofNat_pos]
          -- 316 is positive
          · simp only [Set.mem_Ioi, Nat.ofNat_pos]
          -- 4 ≠ 0
          · linarith only
          -- 5 * 2 ^ (4 - 0) - 1 ≠ 0
          · ring_nf
            linarith only

        -- 2 ^ x * (2 ^ x)⁻¹ = 1
        have pow_mul_inv_eq_one : (2 : ℝ) ^ x * (2 ^ x)⁻¹ = 1 := by
          -- because 2 ^ x ≠ 0
          refine (mul_inv_eq_one₀ ?_).mpr rfl
          refine (Real.rpow_ne_zero ?_ hx).mpr ?_
          all_goals linarith only []

        -- split on sign of 5 * 2 ^ (4 - x) - 1
        rcases lt_trichotomy 0 ((5 : ℝ) * 2 ^ (4 - x) - 1) with h | h | h
        -- if it's positive, we'll find that x = 3
        -- we start by combining logs
        · rw [←Real.log_mul] at aa
          -- arguments to log are positive, so it's injective
          -- we get the equality 4 + 2 ^ (x + 2) = 4 * (5 * 2 ^ (4 - x) - 1)
          have equal := Real.log_injOn_pos ?_ ?_ aa

          -- rewrite it as a quadratic of 2 ^ x
          rw [pow_sub_x, Real.rpow_add] at equal
          ring_nf at equal
          apply_fun (fun s => (2 : ℝ) ^ x * s) at equal
          ring_nf at equal
          rw [pow_mul_inv_eq_one] at equal
          replace equal : 4 * (((2 : ℝ) ^ x) * (2 ^ x)) + 8 * (2 ^ x) + (-320) = 0 := by
            linarith only [equal]

          -- get roots of quadratic
          have split : ((2 : ℝ) ^ x + 10) * ((2 : ℝ) ^ x - 8) = 0 := by
            linarith only [equal]
          -- 2 ^ x = -10 ∨ 2 ^ x = 8
          simp only [mul_eq_zero] at split
          cases' split with h1 h2
          -- -10 is invalid because 2 ^ x is positive
          · have pos : 0 < (2 : ℝ) ^ x + 10 := by positivity
            rw [h1] at pos
            linarith only [pos]
          -- 2 ^ x = 8 means x = 3, so we're done
          · have eqq : (2 : ℝ) ^ x = 8 := by linarith only [h2]
            have logb := (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mpr eqq
            convert_to Real.logb 2 (2 ^ (3 : ℝ)) = x at logb
            congr
            norm_num
            have pos : (0 : ℝ) < 2 := by positivity
            rw [Real.logb_rpow pos] at logb
            exact logb.symm
            all_goals linarith only []

          -- elementary bounds were used in some transformations
          -- 0 < 2
          · linarith only []
          -- 0 < 4 + 2 ^ (x + 2)
          · simp only [Set.mem_Ioi]
            positivity

          -- 0 < 4 * (5 * 2 ^ (4 - x) - 1) because we assumed 0 < 5 * 2 ^ (4 - x) - 1
          · simp only [Set.mem_Ioi]
            positivity
          -- 4 ≠ 0
          · linarith only []
          -- 5 * 2 ^ (4 - x) - 1 ≠ 0 because we assumed 0 < 5 * 2 ^ (4 - x) - 1
          · exact (ne_of_lt h).symm
        -- when 5 * 2 ^ (4 - x) - 1 = 0, there are no solutions
        · rw [pow_sub_x] at h aa
          ring_nf at h
          replace h : ((2 : ℝ) ^ x)⁻¹ = 1 / 80 := by
            linarith only [h]

          replace h : 1 / ((2 : ℝ) ^ x)⁻¹ = 1 / (1 / 80)
            := congrArg (HDiv.hDiv 1) h
          simp only [div_inv_eq_mul, one_mul, one_div] at h

          -- so x = log_2 80
          have logb := (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mpr h
          rw [Real.rpow_add] at aa
          subst logb

          -- we simplify to get Real.log 324 = Real.log 4
          simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, Real.rpow_logb,
            Real.rpow_two] at aa
          ring_nf at aa
          simp only [Real.log_zero, add_zero] at aa

          -- log is injective on positive numbers, so 324 = 4
          have equal := Real.log_injOn_pos ?_ ?_ aa
          -- contradiction
          linarith only [equal]

          -- elementary bounds
          -- 0 < 324
          · simp only [Set.mem_Ioi, Nat.ofNat_pos]
          -- 0 < 4
          · simp only [Set.mem_Ioi, Nat.ofNat_pos]
          -- the rest
          all_goals linarith only
        -- we handle case when log is given negative argument too
        -- maybe not intended as valid case of the problem, but
        -- there's no solution anyway, so it doesn't matter

        -- log (-r) = log r, so we negate argument to make it positive
        · nth_rw 3 [←Real.log_neg_eq_log] at aa
          -- combine logs, which are now both positive
          rw [←Real.log_mul] at aa
          -- log is injective on positive numbers
          have equal := Real.log_injOn_pos ?_ ?_ aa

          -- simplify equality
          rw [pow_sub_x, Real.rpow_add] at equal
          ring_nf at equal
          replace equal : 4 - (4 + (2 : ℝ) ^ x * 4) = (2 ^ x)⁻¹ * 320 := by
            linarith only [equal]
          ring_nf at equal
          replace equal : (2 ^ x) * (-((2 : ℝ) ^ x * 4))
            = (2 ^ x) * ((2 ^ x)⁻¹ * 320) := by
              exact congrArg (HMul.hMul (2 ^ x)) equal
          ring_nf at equal
          rw [pow_mul_inv_eq_one] at equal
          ring_nf at equal
          -- then we have -((2 ^ x) ^ 2 * 4) = 320, but LHS is negative, while RHS is positive
          have neg : -(((2 : ℝ) ^ x) ^ 2 * 4) ≤ 0 := by
            simp only [Left.neg_nonpos_iff, Nat.ofNat_pos,
              mul_nonneg_iff_of_pos_right]
            positivity
          -- contradiction
          linarith only [equal ▸ neg]
          · linarith only
          · simp only [Set.mem_Ioi]
            positivity
          -- elementary bounds, use assumption of 5 * 2 ^ (4 - x) - 1 < 0
          simp only [Set.mem_Ioi]
          apply mul_pos_iff.mpr
          refine Or.inl ?_
          refine ⟨?_, ?_⟩
          all_goals linarith only [h]
      -- x = 3 is a valid solution
      · intro aa
        rw [aa]
        ring_nf
        rw [←(@Real.log_mul 4 9 (by linarith only) (by linarith only))]
        ring_nf