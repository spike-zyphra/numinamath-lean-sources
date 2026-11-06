import Mathlib

open Nat

/-11. (VIE 1) Prove that there exist infinitely many positive integers $n$ such that the decimal representation of $5^{n}$ contains a block of 1976 consecutive zeros.-/

/-We shall show by induction that $5^{2^{k}}-1=2^{k+2} q_{k}$ for each $k=0,1, \ldots$, where $q_{k} \in \mathbb{N}$ -/
lemma lemma1 : ∀ k : ℕ, ∃ q : ℕ, 5 ^ (2 ^ k) - 1 = 2 ^ (k + 2) * q := by
  intro k
  induction k with
  | zero => use 1; norm_num
  | succ k ih => {
    obtain ⟨qk,h1⟩ := ih
    use (5 ^ (2 ^ k) + 1) * qk / 2
    calc
      _ = (5 ^ (2 ^ k)) ^ 2 - 1 ^ 2 := by
        congr 1
        . exact Mathlib.Tactic.Ring.pow_nat rfl rfl rfl
      _ = (5 ^ (2 ^ k) - 1) * (5 ^ (2 ^ k) + 1) := by
        rw[sq_sub_sq,mul_comm]
      _ = 2 ^ (k + 2) * qk * (5 ^ (2 ^ k) + 1) := by
        rw [h1]
      _ = _ := by
        rw [add_assoc k 1 2,add_comm 1 2,←add_assoc k 2 1,pow_add 2 (k+2),pow_one, mul_assoc _ 2]
        have h2 : Even ((5 ^ 2 ^ k + 1) * qk) := by
          apply Even.mul_right
          apply Odd.add_one
          apply Odd.pow
          decide
        rw[two_mul_div_two_of_even h2]
        linarith
  }

theorem number_theory_25083 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ (Nat.digits 10 (5 ^ n)).length ≥ 1976 ∧
      ∃ k : ℕ, (Nat.digits 10 (5 ^ n))[k]? = some 0 ∧
        ∀ i ∈ Finset.range 1976, (Nat.digits 10 (5 ^ n))[k + i]? = some 0 := by
  intro n
  /-make sure k is large enough-/
  let k := Nat.max (n+1) (4*2000 + 1)
  /-properties of k-/
  have h1 : k > 4 * 2000 := by
    have h1 : k ≥ 4 * 2000 + 1 := by exact Nat.le_max_right (n+1) (4 * 2000 + 1)
    linarith
  have h2 : k > n := by
    have h2 : k ≥ n + 1 := by exact Nat.le_max_left (n + 1) (4 * 2000 + 1)
    linarith
  use (2^k+k+2)
  obtain ⟨qk,h3⟩ := lemma1 k
  /-prove that qk obtained from lemma1 is positive-/
  have qkpos : qk > 0 := by
    by_contra h4
    push_neg at h4
    have h5 : qk = 0 := by exact eq_zero_of_le_zero h4
    simp [h5] at h3
    have h6 : k > 4 := by linarith
    have h7 : 2 ^ k > 1 := by calc
      _ > 2 ^ 4 := by
        simp only [gt_iff_lt]
        refine (Nat.pow_lt_pow_iff_right ?_).mpr h6
        norm_num
      _ > 1 := by
        norm_num
    have h8 : 5 ^ (2^k) > 5 ^ 1 := by
      refine (Nat.pow_lt_pow_iff_right ?_).mpr h7
      norm_num
    simp at h8
    have h9 : 5 ^ 2 ^ k ≤ 1 := by
      exact Nat.le_of_sub_eq_zero h3
    linarith
  /-show that (5 ^ (2 ^ k + k + 2)) have desired form-/
  have h4 : (5 ^ (2 ^ k + k + 2)) = 10 ^ (k+2)*qk + 5^(k+2) := by
  /-prove by calculation-/
      rw[add_assoc,pow_add]
      calc
        _ = (5^(2^k)-1+1)*5^(k+2) := by
          congr 1
          have h4 : 5 ^ 2 ^ k ≥ 1 := by
            exact one_le_pow' (2 ^ k) 4
          omega
        _ = (2^(k+2)*qk + 1) * 5 ^ (k+2) := by
          rw[h3]
        _ = 10^(k+2)*qk + 5 ^ (k+2) := by
          rw[add_mul,one_mul];
          congr 1
          rw[mul_assoc,mul_comm qk,←mul_assoc]
          congr 1
          rw[←mul_pow];simp

  /-prove that the digits length of given number is larger than k+2, which is obvious because 10 ^ (k+2) has k+2 0's -/
  have h5 : (digits 10 (10 ^ (k + 2) * qk + 5 ^ (k + 2))).length ≥ k + 2 := by
    calc
      _ ≥ (Nat.digits 10 (10 ^ (k + 2))).length := by
        rw [ge_iff_le]
        apply Nat.le_digits_len_le
        calc
          _ ≤ 10 ^ (k + 2) * qk := by
            simp
            exact qkpos
          _ ≤ 10 ^ (k + 2) * qk + 5 ^ (k + 2) := by
            simp
      _ ≥ k + 2 := by
        have h5 : (10 ^ (k + 2)) < 10 ^ ((digits 10 (10 ^ (k + 2))).length) := by
          apply Nat.lt_base_pow_length_digits
          norm_num
        simp only [ge_iff_le]
        apply le_of_lt
        refine (Nat.pow_lt_pow_iff_right ?_).mp h5
        norm_num
  and_intros
  . /-prove that 2^k+k+2>n-/
    have h3 : 2 ^ k > n := by calc
      _ > 2 ^ n := by
        refine (Nat.pow_lt_pow_iff_right ?_).mpr (h2)
        norm_num
      _ > n := by
        exact Nat.lt_two_pow_self
    linarith
  . /-prove there is at least 1976 digits by h5, which says there is more than k+2 digits-/
    rw[h4]
    calc
      _ ≥ k + 2 := by
        exact h5
      _ ≥ _ := by
        linarith
  . rw [h4]
    /-give the digits where zeros begins-/
    use 3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1
    let addnumlen := (digits 10 (5 ^ (k+2))).length
    /-show that in [addnumlen, k+2), digits[i ] = 0-/
    have h7 : ∀ i ≥ addnumlen, (i<k+2) → (digits 10 (10 ^ (k + 2) * qk + 5 ^ (k + 2)))[i]? = some 0 := by
      intro i h7 h8
      calc
        _ = (digits 10 (10 ^ (addnumlen + ((k + 2) - addnumlen)) * qk + 5 ^ (k + 2)))[i]? := by
          congr 5
          omega
        _ = (digits 10 (5^(k+2)) ++ List.replicate (k+2-addnumlen) 0 ++ digits 10 qk)[i]? := by
          congr 1; rw[add_comm _ (5^(k+2))]
          rw[←Nat.digits_append_zeroes_append_digits (by norm_num) qkpos]
        _ = (digits 10 (5^(k+2)) ++ List.replicate (k+2-addnumlen) 0)[i]? := by
          apply List.getElem?_append_left
          simp[addnumlen]
          omega
        _ = (List.replicate (k+2-addnumlen) 0)[i-addnumlen]? := by
          apply List.getElem?_append_right
          exact h7
        _ = some 0 := by
          refine List.getElem?_replicate_of_lt ?_
          omega
    /-give the upper bound of addnumlen-/
    have h8 : 3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1 ≥ addnumlen := by
      simp
      calc
      /-prove by showing (5 ^ (k + 2)) ≤ 10 ^ (3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1) -/
        _ ≤ (digits 10 (10^(3 * (Nat.ceil (((k:ℝ)+2)/4))))).length := by
          unfold addnumlen
          apply Nat.le_digits_len_le
          calc
            _ ≤ (5 ^ 4) ^ (Nat.ceil (((k:ℝ) + 2)/4)) := by
              rw[←Nat.pow_mul]
              apply Nat.pow_le_pow_right
              . norm_num
              . rify
                calc
                  _ = 4 * (((k:ℝ) + 2)/4) := by
                    linarith
                  _ ≤ _ := by
                    refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                    . norm_num
                    . exact le_ceil (((k:ℝ) + 2) / 4)
                    . norm_num
                    . exact cast_nonneg' ⌈((k:ℝ) + 2) / 4⌉₊
            _ ≤ (10^3) ^ (Nat.ceil (((k:ℝ) + 2)/4)) := by
              refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
              . refine Nat.ne_zero_iff_zero_lt.mpr ?_
                refine ceil_pos.mpr ?_
                rify at h1
                linarith
              . norm_num
            _ = (10^(3 * (Nat.ceil (((k:ℝ)+2)/4)))) := by
              exact (Nat.pow_mul 10 3 ⌈((k:ℝ) + 2) / 4⌉₊).symm
        _ = (digits 10 ((10 ^ (3 * ⌈((k:ℝ) + 2) / 4⌉₊))*1)).length := by
          congr
          simp
        _ = (List.replicate (3 * ⌈((k:ℝ) + 2) / 4⌉₊) 0 ++ digits 10 1).length := by
          congr
          apply Nat.digits_base_pow_mul
          norm_num
          norm_num
        _ = _ := by simp
    /-basic face about ceil, used by following linarithes-/
    have h9 : (Nat.ceil (((k:ℝ)+2)/4)) < (((k:ℝ)+2)/4) + 1 := by
      refine ceil_lt_add_one ?_
      refine div_nonneg ?_ ?_
      linarith
      norm_num
    /-show that 3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1 + i fall in range [addnumlen, k+2)-/
    have h10 : (3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1) < k + 2 := by
      rify
      rify at h1
      linarith
    and_intros
    /-the goal following from h7-/
    . exact h7 ((3 * (Nat.ceil (((k:ℝ)+2)/4)))+1) h8 h10
    . intro i hi
      simp at hi
      have h11 : 3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1 + i < k + 2 := by
        rify at hi h1
        rify
        linarith[h10]
      have h12 : 3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1 + i ≥ addnumlen := by
        simp
        linarith
      exact h7 (3 * (Nat.ceil (((k:ℝ)+2)/4)) + 1 + i) h12 h11
