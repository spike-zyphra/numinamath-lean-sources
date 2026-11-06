import Mathlib

open Finset Real

/- No integer is equal to (2 * k + 1) * Real.pi / 2, for any k ∈ ℤ. -/
lemma Nat_ne_odd_mul_pi_div_two (z : ℤ) (k : ℤ) : (z : ℝ) ≠ (2 * k + 1) * Real.pi / 2 := by
  -- RHS is irrational
  have rhs_irrational : Irrational ((2 * (k : ℝ) + 1) * Real.pi / 2) := by
      convert_to Irrational ((2 * k + 1 : ℤ) * (Real.pi / (2 : ℕ)))
      · norm_cast
        ring_nf
      exact (irrational_pi.div_nat (by omega)).int_mul (by omega)

  -- LHS is rational
  have lhs_rational : ¬Irrational (z : ℝ) := by norm_num

  -- assuming they are equal leads to a contradiction
  by_contra eq
  rw [eq] at lhs_rational
  contradiction

/- Given any natural number k, then tan 1 is equal to
  (tan k - tan (k - 1)) / (1 + tan k * tan (k - 1)) -/
lemma Real_tan_one_nat (k : ℕ)
  : Real.tan 1 = (Real.tan k - Real.tan (k - 1)) / (1 + Real.tan k * Real.tan (k - 1)) := by

    -- consider 1 as k + -(k - 1)
    trans Real.tan (k + -(k - 1))
    · ring_nf
    -- use addition formula
    rw [Real.tan_add']

    -- simplify
    rw [Real.tan_neg]
    ring

    -- consider both arguments
    split_ands
    -- k works
    · intro k2
      exact Nat_ne_odd_mul_pi_div_two k k2
    -- -(k - 1) works
    · intro k2
      convert Nat_ne_odd_mul_pi_div_two (-(k - 1)) k2
      norm_cast

/- if tan a = tan b
  and none of a and b are equal to (2 * k + 1) * π / 2 for some k -/
lemma Real_tan_eq {a b : ℝ} (h : Real.tan a = Real.tan b)
  (ha : ∀ (k : ℤ), a ≠ (2 * k + 1) * Real.pi / 2)
  (hb : ∀ (k : ℤ), b ≠ (2 * k + 1) * Real.pi / 2)
  : ∃ k : ℤ, a = b + k * Real.pi := by

    -- we'll use that tan is periodic

    -- π is positive
    have half_pos : 0 < π := by positivity

    -- let a = a' + ka * π
    -- and b = b' + kb * π, where a', b' ∈ [-π / 2, -(π / 2) + π)
    let a' := toIcoMod half_pos (-(π / 2)) a
    let b' := toIcoMod half_pos (-(π / 2)) b
    let ka := toIcoDiv half_pos (-(π / 2)) a
    let kb := toIcoDiv half_pos (-(π / 2)) b

    have a_eq : a' + ka • π = a := toIcoMod_add_toIcoDiv_zsmul half_pos (-(π / 2)) a
    have b_eq : b' + kb • π = b := toIcoMod_add_toIcoDiv_zsmul half_pos (-(π / 2)) b
    simp only [zsmul_eq_mul] at a_eq b_eq

    have mem_a : a' ∈ Set.Ico (-(π / 2)) (-(π / 2) + π) := toIcoMod_mem_Ico half_pos (-(π / 2)) a

    have mem_b : b' ∈ Set.Ico (-(π / 2)) (-(π / 2) + π) := toIcoMod_mem_Ico half_pos (-(π / 2)) b


    -- then we have that tan a' = tan b'
    simp only [←a_eq, ←b_eq, Real.tan_add_int_mul_pi] at h

    -- none of a' and b' are -π / 2
    have a'_ne : a' ≠ -(π / 2) := by
      by_contra eqq
      replace ha := eqq ▸ a_eq ▸ ha (ka - 1)
      push_cast at ha
      ring_nf at ha
      tauto

    have b'_ne : b' ≠ (-(π / 2)) := by
      by_contra eqq
      replace ha := eqq ▸ b_eq ▸ hb (kb - 1)
      push_cast at ha
      ring_nf at ha
      tauto

    -- so a', b' ∈ (-π / 2, -(π / 2) + π)
    replace mem_a : a' ∈ Set.Ioo (-(π / 2)) (-(π / 2) + π) := by
      convert_to a' ∈ (Set.Ico (-(π / 2)) (-(π / 2) + π)) \ {-(π / 2)}
      · exact Eq.symm Set.Ico_diff_left
      tauto

    replace mem_b : b' ∈ Set.Ioo (-(π / 2)) (-(π / 2) + π) := by
      convert_to b' ∈ (Set.Ico (-(π / 2)) (-(π / 2) + π)) \ {-(π / 2)}
      · exact Eq.symm Set.Ico_diff_left
      tauto

    -- using the injectivity of tan, we have a' = b'
    have a'_eq_b' : a' = b' := by
      simp only [Set.mem_Ioo, lt_neg_add_iff_add_lt] at mem_a
      simp only [Set.mem_Ioo, lt_neg_add_iff_add_lt] at mem_b
      apply Real.tan_inj_of_lt_of_lt_pi_div_two
      · tauto
      · linarith
      · tauto
      · linarith
      · exact h

    -- then we just need to show that b' + ka * π = b' + kb * π + k * π, for some k
    rw [←a_eq, ←b_eq, a'_eq_b']
    -- k = ka - kb works
    exists ka - kb
    push_cast
    ring

/- tan 1 is non-zero -/
lemma Real_tan_one_ne_zero : tan 1 ≠ 0 := by
    -- we just need to prove that k * π / 2 ≠ 1, for all k
    refine tan_ne_zero_iff.mpr ?_
    intro k

    -- consider when k is zero
    by_cases k_eq : k = 0
    -- that's impossible
    · simp only [k_eq, Int.cast_zero, zero_mul, zero_div, ne_eq, zero_ne_one,
      not_false_eq_true]

    -- write in a form which makes irrationality clear
    convert_to k * (π / (2 : ℕ)) ≠ 1
    · ring

    -- the LHS is irrational
    have lhs_irrational : Irrational (k * (π / (2 : ℕ)))
      := (irrational_pi.div_nat (by omega)).int_mul k_eq

    -- but the RHS is rational
    have rhs_rational : ¬Irrational (1 : ℝ) := by norm_num

    -- that's a contradiction
    by_contra eqq
    rw [eqq] at lhs_irrational
    contradiction

/- If k is a natural number, then tan k - tan (k - 1) is non-zero. -/
lemma Real_tan_nat_sub_sub (k : ℕ) : tan k - tan (k - 1) ≠ 0 := by
    -- assume it's equal to zero
    by_contra eqq
    -- then we have that tan k = tan (k - 1)
    have tan_eq : tan k = tan (k - 1) := by linarith
    -- k and k - 1 are not equal to (2 * k_1 + 1) * π / 2 for any k_1
    have k_ne := Nat_ne_odd_mul_pi_div_two k
    have k_pred_ne := Nat_ne_odd_mul_pi_div_two (k - 1)
    push_cast at k_pred_ne

    -- so there is a k_2 such that k = k - 1 + k_2 * π
    obtain ⟨k2, kh⟩ := Real_tan_eq tan_eq k_ne k_pred_ne

    -- so we have that k_2 * π = 1
    have rearr : 1 = k2 * π := by linarith

    -- so k_2 is not zero
    by_cases k2_eq_zero : k2 = 0
    · simp only [k2_eq_zero, Int.cast_zero, zero_mul, one_ne_zero] at rearr

    -- but then 1 / k_2 = π
    have pi_eq : 1 / k2 = π := by
      field_simp
      linarith

    -- but the LHS is rational
    have lhs_rat : ¬Irrational (1 / k2 : ℝ) := by simp only [one_div,
      irrational_inv_iff, Int.not_irrational, not_false_eq_true]
    -- while the RHS is irrational
    have rhs_irrat : Irrational (Real.pi) := irrational_pi

    -- which is a contradiction
    rw [pi_eq] at lhs_rat
    contradiction

/- 17.2. (CSSR, 72). Prove that there exist numbers $A$ and $B$, satisfying for any value of $n \in \mathbf{N}$ the equality


$$

a_{\mathbf{i}}+a_{2}+\ldots+a_{n}=A \operatorname{tg} n+B n

$$


where it is denoted


$$

a_{k}=\operatorname{tg} k \operatorname{tg}(k-1)

$$
 -/
theorem algebra_123407 {a : ℕ → ℝ}
    (ha : ∀ k, a k = tan k * tan (k - 1)) :
    ∃ A B, ∀ n, ∑ i ∈ Icc 1 n, a i = A * tan n + B * n := by
    -- we can simplify the sum to tan n / tan 1 - n
    have sum_eq : ∀ n, ∑ i ∈ Icc 1 n, a i = tan n / tan 1 - n := by
      intro n
      -- consider when n is zero
      by_cases hn : n = 0
      · subst hn
        -- then both sides are zero
        simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty, CharP.cast_eq_zero, tan_zero,
          zero_div, sub_self]

      -- so let n be non-zero

      -- so write n as n + 1
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero hn

      -- chain equalities
      calc
        -- use definition of a_i
        _ = ∑ k ∈ Icc 1 (n + 1), tan k * tan (k - 1) := by simp_rw [ha]
        -- use tan 1 = (tan k - tan (k - 1)) / (1 + tan k * tan (k - 1))
        -- to show that
        -- tan k * tan (k - 1) = (tan k - tan (k - 1)) / tan 1 - 1
        _ = ∑ k ∈ Icc 1 (n + 1), ((tan k - tan (k - 1)) / tan 1 - 1) := by
          congr
          ext k
          rw [Real_tan_one_nat k]
          -- tan k - tan (k - 1) is non-zero
          have denom_ne_zero : tan k - tan (k - 1) ≠ 0 := Real_tan_nat_sub_sub k

          -- so we can simplify
          field_simp
        -- split into three terms
        _ = ∑ k ∈ Icc 1 (n + 1), (tan k / tan 1 - tan (k - 1) / tan 1 - 1) := by
          congr
          ext i
          have tan_one_ne_zero := Real_tan_one_ne_zero
          ring_nf
        -- seperate terms into seperate terms
        _ = ∑ k ∈ Icc 1 (n + 1), tan k / tan 1 - ∑ k ∈ Icc 1 (n + 1), tan (k - 1) / tan 1 - ∑ k ∈ Icc 1 (n + 1), 1 := by
          simp only [Finset.sum_sub_distrib]
        -- change second sum into more convenient form
        -- ∑ i ∈ [1, n + 1] f(k - 1) = ∑ i ∈ [0 + 1, (n + 1) + 1), f(k - 1)
        _ = ∑ k ∈ Icc 1 (n + 1), tan k / tan 1 - ∑ k ∈ Ico (0 + 1) ((n + 1) + 1), (fun i : ℕ => tan i / tan 1) (k - 1) - ∑ k ∈ Icc 1 (n + 1), 1 := by
          congr 2
          apply Finset.sum_congr
          exact rfl
          simp only [zero_add, mem_Ico, and_imp]
          intro x xh hx
          congr
          norm_cast
        -- simplify it further using ∑ i ∈ [0 + 1, (n + 1) + 1), f (k - 1) = ∑ i ∈ [0, n + 1), f(k)
        _ = ∑ k ∈ Icc 1 (n + 1), tan k / tan 1 - ∑ k ∈ Ico 0 ((n + 1)), (fun i : ℕ => tan i / tan 1) k - ∑ k ∈ Icc 1 (n + 1), 1 := by
          rw [Finset.sum_Ico_add_right_sub_eq (f := (fun i : ℕ => tan i / tan 1)) 0 (n + 1) 1]

        -- separate first term from first sum
        _ = (tan (n + 1) / tan 1 + ∑ k ∈ Icc 1 n, tan k / tan 1) - ∑ k ∈ Ico 0 ((n + 1)), (fun i : ℕ => tan i / tan 1) k - ∑ k ∈ Icc 1 (n + 1), 1 := by
          simp only [Nat.Ico_zero_eq_range, sum_const, Nat.card_Icc, add_tsub_cancel_right,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, sub_left_inj]
          rw [Finset.sum_Icc_succ_top]
          norm_cast
          linarith
          omega
          -- simplify middle sum
        _ = (tan (n + 1) / tan 1 + ∑ k ∈ Icc 1 n, tan k / tan 1) - ∑ k ∈ Icc 0 n, tan k / tan 1 - ∑ k ∈ Icc 1 (n + 1), 1 := by congr
        -- ignore first term of second sum, because it's equal to 0
        _ = (tan (n + 1) / tan 1 + ∑ k ∈ Icc 1 n, tan k / tan 1) - ∑ k ∈ Icc 1 n, tan k / tan 1 - ∑ k ∈ Icc 1 (n + 1), 1 := by
          congr 2
          -- one sum is a subset of the other sum
          have subs : Icc 1 n ⊆ Icc 0 n := by
            refine Icc_subset_Icc_left ?_
            omega
          refine Eq.symm ?_
          apply Finset.sum_subset subs

          -- and all the other terms are equal to zero
          intro x xh hx
          simp only [mem_Icc, zero_le, true_and, not_and, not_le] at xh hx

          -- consider the first term
          by_cases x_eq : x = 0
          -- it's zero
          · norm_num [x_eq]
          -- all other terms are part of both sums
          · have x_pos : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr x_eq
            replace hx := hx x_pos
            linarith
        -- cancel equal sums
        _ = tan (n + 1) / tan 1 - ∑ k ∈ Icc 1 (n + 1), 1 := by ring
        -- simplify
        _ = tan (n + 1 : ℕ) / tan 1 - (n + 1 : ℕ) := by norm_num

    -- so we see that A = 1 / tan 1 and B = -1 works
    exists 1 / tan 1, -1
    intro n
    -- use our sum equality
    rw [sum_eq n]
    ring