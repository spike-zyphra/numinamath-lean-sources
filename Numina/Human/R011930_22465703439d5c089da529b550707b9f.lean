import Mathlib

open Real

theorem algebra_84734 :
    IsGreatest {y | ∃ x, 0 < y ∧ logb 10 (x ^ y) = (logb 10 x) ^ y ∧ x > 10 ^ (3 / 2 : ℝ)} 4 := by 
    --to prove the claim it suffices to show that 4 is the greatest number among the y so that there exist a real number b with bʸ=yb and b>3/2.
    suffices IsGreatest {y : ℕ | ∃ b : ℝ, 0 < y ∧  b ^ ((y : ℝ)- 1) = y ∧ b > 3 / 2} 4 by
        unfold IsGreatest at this ⊢
        simp at this ⊢
        obtain ⟨⟨b, hb⟩, hupperb⟩ := this
        constructor 
        --this is because one can use 10^b as x in the previous set, and recover all conditions correctly
        · use ((10 : ℝ) ^ b)
          constructor
          --by algebraic passagges and by the fact that log_c (c ^ a) = a, one shows the identity
          · rw[logb_pow 10 (10 ^ b) 4, logb_rpow (by linarith) (by linarith)]
            push_cast
            rw[← hb.1]
            norm_num
            nth_rw 2 [← rpow_one b]
            rw[← rpow_add (by linarith) 3 1]
            ring_nf
            norm_cast
          --again by log_c (c ^ a) = a one shows that the bound x > 10 ^ (3/2) holds.
          · rw[rpow_lt_rpow_left_iff (by linarith)]
            exact hb.2
        --it is also the upper bound by analogous reasoning
        · unfold upperBounds at hupperb ⊢
          simp at hupperb ⊢
          intro a ha x heqx hboundx
          specialize hupperb ha (logb 10 x)
          have num_pos : (10 : ℝ) ^ (3 / 2 : ℝ) > 0 := by 
            rw[gt_iff_lt, ← @rpow_lt_rpow_iff _ _ 2 (by linarith) (rpow_nonneg (by linarith) (3 / 2 : ℝ)) (by linarith)]
            rw[← rpow_mul (by linarith)]
            norm_num
          have log_ne_zero : logb 10 x ≠ 0 := by
            by_contra log_eq_0
            rw[logb_eq_zero] at log_eq_0
            simp at log_eq_0
            obtain opt1|opt2|opt3|opt4 := log_eq_0
            · linarith
            · rw[opt2] at hboundx
              linarith
            · rw[opt3] at hboundx
              rw[← @rpow_lt_rpow_iff _ _ 2 (rpow_nonneg (by linarith) (3 / 2 : ℝ)) (by linarith) (by linarith)] at hboundx
              rw[← rpow_mul (by linarith)] at hboundx
              norm_num at hboundx
            · rw[opt4] at hboundx
              linarith
          rw[logb_pow 10 x a] at heqx
          rw[rpow_sub_one log_ne_zero] at hupperb
          norm_cast at hupperb
          rw[← heqx, mul_div_assoc, div_self log_ne_zero] at hupperb
          norm_num at hupperb
          rw[← @rpow_lt_rpow_left_iff 10 _ _ (by linarith), rpow_logb (by linarith) (by linarith) (by linarith)] at hupperb
          specialize hupperb hboundx
          exact hupperb 
    unfold IsGreatest
    simp
    constructor
    --4 is an element of the new set using b = 4 ^ (1/3), in fact by sustituting it directly in alle the equalties/inequalities they hold
    · use (4 ^ (1 / 3 : ℝ))
      constructor
      --4 ^ (1/3) ^ (4-1) = 4 by properties of the powers. 
      · norm_num
        rw[← rpow_mul (by linarith) (1 / 3) 3]
        norm_num
      --4 ^ (1/3) is bigger than 3/2
      · rw[← @rpow_lt_rpow_iff _ _ 3 (by linarith) (rpow_nonneg (by linarith) (1 / 3)) (by linarith)]
        rw[← rpow_mul (by linarith)]
        norm_num
    --4 is also the upper bound of the set
    · unfold upperBounds
      simp
      intro y ypos b eqb blowbound
      symm at eqb
      --if y = 1, y ≤ 4 is trivially satisfied
      by_cases hy : y = 1
      · rw[hy]
        linarith
      · push_neg at hy
        rw[← rpow_inv_eq (by norm_cast; exact le_of_lt ypos) (by linarith) (by rw[sub_ne_zero]; norm_cast)] at eqb
        rw[← eqb] at blowbound
        --for y bigger than 1 it suffices to show that whenever we consider y greater than 5, then the bound b > 3/2 stops to hold.
        suffices y ≥ 5 → (y : ℝ) ^ (1 / ((y : ℝ) - 1)) ≤ 3 / 2 by
            by_cases hy' : y < 5
            · linarith
            · push_neg at hy'
              specialize this hy'
              field_simp at blowbound
              exfalso
              linarith
        let f := fun (y : ℕ) => if y = 0 ∨ y = 1 then 2 else (y : ℝ) ^ (1 / ((y : ℝ) - 1))
        --this is true because the function f := y ↦ y ^ (1 / (y-1)) is well defined and antitone, meaning it continuously decreases.
        suffices ∀ (n : ℕ), f (n + 1) ≤ f n by
            have antitonef : Antitone f := by exact antitone_nat_of_succ_le this
            intro hyge5
            specialize antitonef hyge5
            simp[f] at antitonef
            norm_num at antitonef
            --we have that f (5) < 3/2, hence f(y) < 3/2 forall y ≥ 5, forcing y ≤ 4 and hence the claim
            have boundf5: (5 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 / 2 : ℝ) := by 
                rw[← @rpow_le_rpow_iff _ _ 4 (rpow_nonneg (by linarith) (1 / 4)) (by linarith) (by linarith)]
                rw[← rpow_mul (by linarith)]
                norm_num
            have yne0or1: ¬ (y = 0 ∨ y = 1) := by push_neg; exact ⟨by linarith, by linarith⟩
            simp[yne0or1] at antitonef
            field_simp at antitonef
            linarith
        --to prove the antitonicity of f, we proceed by induction on n
        intro n
        induction' n with k hk
        · simp[f]
        --in the case 0 the function is defined ad hoc
        · by_cases hf1 : k = 0
          · rw[hf1]
            simp[f]
            ring_nf
            linarith
          --same for the case f(1)
          · by_cases hf2 : k = 1
            · rw[hf2]
              simp[f]
              norm_num
              rw[← @rpow_le_rpow_iff _ _ 2 (rpow_nonneg (by linarith) (1 / 2)) (by linarith) (by linarith)]
              rw[← rpow_mul (by linarith)]
              norm_num
            --in any other case we solve the equivalent (k + 2) ^ k ≤ (k + 1) ^ (k + 1)
            · have kne0or1: ¬ (k = 0 ∨ k = 1) := by push_neg at hf1 hf2 ⊢; exact ⟨hf1,hf2⟩
              simp[f, kne0or1, hf1, hf2] at hk ⊢
              rw[← @rpow_le_rpow_iff _ _ (((k : ℝ) + 1) * (k : ℝ)) (rpow_nonneg (by norm_cast; exact le_of_lt (Nat.succ_pos k.succ)) (Inv.inv ((k : ℝ) + 1))) (rpow_nonneg (by norm_cast; exact le_of_lt (Nat.succ_pos k)) (Inv.inv (k : ℝ))) (mul_pos (by linarith) (by norm_cast; exact Nat.pos_of_ne_zero hf1))]
              rw[← rpow_mul (by linarith)]
              rw[← rpow_mul (by linarith)]
              field_simp
              ring_nf
              rw[← rpow_natCast]
              --we rewrithe the LHS as (k + 1) ^ k * (1 + 1 / (k + 1)) ^ k
              rw[(by field_simp; ring_nf : (2 + (k : ℝ)) ^ (k : ℝ) = (k + 1) ^ (k : ℝ) * (1 + 1 / (k + 1)) ^ (k : ℝ))]
              --now it suffices to show that (1 + 1/(k + 1)) ^ k ≤ e
              suffices (1 + 1 / ((k : ℝ) + 1)) ^ (k : ℝ) ≤ exp 1 by
                --this is true because for k ≥ 2, e is always ≤ k + 1
                have e_le_k_add_one : exp 1 ≤ (k : ℝ) + 1 := by 
                  have k_ge_two : k + 1 ≥ 3 := by omega
                  rify at k_ge_two
                  have three_gt_e : (3 : ℝ) > 2.7182818286 := by norm_num
                  exact le_of_lt (LT.lt.trans (exp_one_lt_d9) (lt_of_lt_of_le three_gt_e k_ge_two))
                --then, by explicit calculation one shows the final result
                calc
                  ((k : ℝ) + 1) ^ (k : ℝ) * (1 + 1 / ((k : ℝ) + 1)) ^ (k : ℝ) ≤ ((k : ℝ) + 1) ^ (k : ℝ) * exp 1 := by exact mul_le_mul_of_nonneg_left this (rpow_nonneg (by linarith) (k : ℝ))
                  _ ≤ ((k : ℝ) + 1) ^ (k : ℝ) * ((k : ℝ) + 1) := by exact mul_le_mul_of_nonneg_left e_le_k_add_one (rpow_nonneg (by linarith) (k : ℝ))
                  _ = (1 + (k : ℝ)) ^ (1 + (k : ℝ)) := by rw[add_comm 1 (k : ℝ)]; norm_cast
              rw[add_comm]
              --the proof of the claim follows from the approximation 1 + x ≤ e ^ x applied to x = 1 / (k + 1) and the fact that the exponentiation is monotone increasing
              have rpow_le_rpow_succ : (1 / ((k : ℝ) + 1) + 1) ^ (k : ℝ) ≤ (1 / ((k : ℝ) + 1) + 1) ^ ((k : ℝ) + 1) := by exact le_of_lt (rpow_lt_rpow_of_exponent_lt (by nth_rw 1 [← zero_add 1]; exact add_lt_add_right (one_div_pos.mpr (by linarith)) 1) (by linarith))
              have exp_bound : (1 / ((k : ℝ) + 1) + 1) ^ ((k : ℝ) + 1) ≤ exp (1 / ((k : ℝ) + 1)) ^ ((k : ℝ) + 1) := by exact rpow_le_rpow (add_nonneg (le_of_lt (one_div_pos.mpr (by linarith))) (by linarith)) (add_one_le_exp (1 / ((k : ℝ) + 1))) (by linarith)
              rw[← exp_mul (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1), mul_comm, ← mul_div_assoc, mul_one, div_self (by linarith)] at exp_bound
              linarith