import Mathlib

open Nat

lemma nat_le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega


lemma nat_div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [nat_le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega


lemma nat_div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, nat_div_le_iff_le_mul h]


-- the digits sum of (2 ^ n - 1) is n, namely 11...11
lemma sum_digits_aux0 (n : ℕ) : (digits 2 ((2 ^ n - 1))).sum = n  := by 
  induction n with 
  | zero => 
    simp
  | succ k ih => 
    have pos : 2 ^ (k + 1) - 1 > 0 := by 
      have pos1 : 2 ^ (k + 1) > 1 := by 
        exact one_lt_two_pow' k
      omega
    have ge : 2 ≥ 2 := by simp
    obtain h1 := digits_of_two_le_of_pos ge pos 
    have eq1 : ((2 ^ (k + 1) - 1) / 2) = 2 ^ k - 1 := by 
      refine (nat_div_eq_iff ?_).mpr ?_ 
      linarith
      constructor
      · omega
      omega
    have eq2 : (2 ^ (k + 1) - 1) % 2 = 1 := by 
      omega
    simp [h1, eq1, eq2, ih]
    ring_nf


-- the digits sum of (2 ^ n - 1) * 2 is n, namely 11...110, the last digits is zero
lemma sum_digits_aux (n : ℕ) : (digits 2 ((2 ^ n - 1) * 2)).sum = n := by 
  induction n with 
  | zero => 
    simp
  | succ k ih => 
    have pos : 2 ^ (k + 1) - 1 > 0 := by 
      have pos1 : 2 ^ (k + 1) > 1 := by 
        exact one_lt_two_pow' k
      omega
    have pos2 : (2 ^ (k + 1) - 1) * 2 > 0 := by 
      positivity
    have ge : 2 ≥ 2 := by simp
    obtain h1 := digits_of_two_le_of_pos ge pos2
    have eq1 : (2 ^ (k + 1) - 1) * 2 / 2 = (2 ^ (k + 1) - 1) := by 
      omega
    have eq2 : (2 ^ (k + 1) - 1) * 2 % 2 = 0 := by 
      omega
    obtain h2 := sum_digits_aux0 (k)
    have eq3 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by 
      refine (nat_div_eq_iff ?_).mpr ?_ 
      linarith
      constructor
      · omega
      omega
    simp [h1, eq1, eq2, eq3, h2]
    ring

-- for all k ≥ 4, 2 ^ k ≥ k ^ 2
lemma pow_ge_sq_aux (k : ℕ) (h : k ≥ 4): 2 ^ k ≥ k ^ 2 := by
  induction' h with n ih1 ih2
  · linarith
  · simp
    rw [pow_add]
    simp at ih1
    have ineq : 2 * n ^ 2 ≥ (n + 1) ^ 2 := by 
      have ineq2 : (2 : ℝ) * n ^ 2 ≥ (n + 1) ^ 2 := by 
        calc 
          _ ≥  ((n + 1) / n : ℝ ) ^ 2 * n ^ 2 := by 
            have ineq_aux : 2 ≥ ((n + 1) / n : ℝ ) ^ 2 := by 
              have aux : ((n : ℝ) + 1) / (n : ℝ) ≤ 5 / 4 := by 
                calc 
                  _ = 1 + 1 / (n : ℝ) := by 
                    field_simp
                  _ ≤ 1 + 1 / (4 : ℝ) := by
                    simp
                    refine inv_anti₀ ?_ ?_
                    linarith
                    norm_cast
                  _ = _ := by 
                    field_simp
                    norm_num
              have aux2 : (((n : ℝ) + 1) / ↑n) ^ 2 ≤ (5 / 4) ^ 2 := by 
                refine (sq_le_sq₀ ?_ ?_).mpr aux
                positivity
                norm_num
              linarith
            refine mul_le_mul ineq_aux ?_ ?_ ?_
            simp
            positivity
            linarith
          _ = _ := by 
            field_simp
            
      norm_cast at ineq2
    linarith



lemma pow_ge_self (k : ℕ) : 2 ^ k ≥ k := by 
  induction k with 
  | zero => 
    simp
  | succ n ih => 
    by_cases hn0 : n = 0
    · rw [hn0]
      simp
    · have nge1 : n ≥ 1 := by omega
      rw [pow_add]
      linarith
    

theorem number_theory_635147 {a k : ℕ} (ha : 2 ≤ a) (hk : 0 < k) :
  ∃ m : ℕ, m > k ^ k ∧ m = a ^ k + (Nat.factorization (m !) 2) := by 
  use (2 ^ (a ^ k) - 1) * 2
  constructor
  · -- the original solution take (2 ^ (a ^ k) - 1), but it need a very complicated discussion, I change to take (2 ^ (a ^ k) - 1) * 2 which can avoid this discussion.
    have ineq2 : (2 : ℝ) ^ (a ^ k : ℝ) ≥ k ^ (k : ℝ) := by 
      have ineq3 : a ^ k ≥ Real.logb 2 (k ^ (k : ℝ)) := by 
        have eq1 : Real.logb 2 (k ^ (k : ℝ)) = k * Real.logb 2 k := by 
          refine Real.logb_rpow_eq_mul_logb_of_pos ?_
          norm_cast 
        rw [eq1]
        have ineq5 : (a : ℝ) ^ k ≥ (2 : ℝ) ^ k := by 
          refine pow_le_pow_left₀ ?_ ?_ k
          linarith
          norm_cast
        have ineq4 : (2 : ℝ) ^ k ≥ k * Real.logb 2 k := by 
          by_cases hk1 : k = 1 
          simp [hk1]
          by_cases hk2 : k = 2
          simp [hk2]
          linarith
          by_cases hk3 : k = 3
          simp [hk3]
          have aux1 : Real.logb 2 3 ≤ 2 := by 
            refine (Real.logb_le_iff_le_rpow ?_ ?_).mpr ?_
            linarith
            linarith
            linarith
          linarith
          have kge4 : k ≥ 4 := by
            omega
          obtain h1 := pow_ge_sq_aux k kge4
          norm_cast 
          norm_num 
          have kgelog : (k : ℝ) ≥ Real.logb 2 k := by 
            refine (Real.logb_le_iff_le_rpow ?_ ?_).mpr ?_
            linarith
            norm_cast
            norm_cast
            exact pow_ge_self k
          calc 
            _ ≤ (k : ℝ) * k := by 
              nlinarith
            _ ≤ _ := by 
              norm_cast
              rw [show k * k = k ^ 2 by ring]
              exact h1
        nlinarith
      have ge1 : 2 > (1 : ℝ) := by norm_num
      refine (Real.logb_le_iff_le_rpow ge1 ?_).mp ineq3
      positivity
    have ineq1 : (2 : ℤ) ^ a ^ k ≥ k ^ k := by 
      norm_cast at ineq2
      norm_cast
    zify
    rw [Nat.cast_sub]
    have pos : 2 ^ a ^ k - (2 : ℤ) > 0 := by 
      have aux1 : 2 ^ a ^ k > 2 ^ 1 := by
        refine Nat.pow_lt_pow_of_lt ?_ ?_
        linarith
        refine Nat.one_lt_pow ?_ ha
        linarith
      linarith
    simp
    linarith
    exact Nat.one_le_two_pow
  · -- second part, (2 ^ a ^ k - 1) * 2 = a ^ k + ((2 ^ a ^ k - 1) * 2)!.factorization 2, by using the result that `(p - 1) * padicValNat p n ! = n - (p.digits n).sum` where p is prime.
    have prime1 : Nat.Prime 2 := by norm_num
    have neq2 : ((2 ^ a ^ k - 1) * 2)! ≠ 0 := by 
      exact factorial_ne_zero ((2 ^ a ^ k - 1) * 2)
    have pos : ((2 ^ a ^ k - 1) * 2)!  > 0 := by 
      exact factorial_pos ((2 ^ a ^ k - 1) * 2)
    obtain h1 := multiplicity_eq_factorization prime1 neq2
    rw [←h1, ←padicValNat_def' (by norm_num) pos]
    have prime2 : Fact (Nat.Prime 2) := by 
      exact fact_prime_two
    obtain h2 := @sub_one_mul_padicValNat_factorial 2 prime2 ((2 ^ a ^ k - 1) * 2)
    simp at h2
    rw [h2, sum_digits_aux]
    zify
    repeat rw [Nat.cast_sub]
    norm_num
    ring_nf
    have aux : a ^ k ≤ (2 ^ a ^ k - 1) := by
      refine le_sub_one_of_lt ?_
      exact Nat.lt_two_pow_self
    linarith
    exact Nat.one_le_two_pow
    