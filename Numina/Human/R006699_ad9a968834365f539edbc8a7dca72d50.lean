import Mathlib

-- Let $k$ be a positive integer and $M$ be a positive integer greater than 1. The increasing sequence $3,15,24,48,\dots$ consists of those positive multiples of 3 that are one less than a perfect square. Let $a_k$ denote the $k$-th term of this sequence. Determine the remainder when $a_k$ is divided by $M$. Show the answer is $(((\lfloor k/2 \rfloor \cdot 3 + (k \pmod 2) + 1)^2 - 1) \pmod M)$.
namespace number_theory_640280

lemma n_sq_ge_1 k : ((k / 2) * 3 + k % 2 + 1)^2 ≥ 1 := by
  have : (k / 2) * 3 + k % 2 + 1 ≥ 1 := by
    simp --linarith
  nlinarith

lemma nth_multiple_of_3_and_eq_square_sub_1_eq : (k : ℕ) →
    Nat.nth (fun m => 3 ∣ m ∧ ∃ n, m = n^2 - 1) k = ((k / 2) * 3 + k % 2 + 1)^2 - 1
  | 0 => by
    norm_num
    rw [Nat.nth_zero]
    apply IsLeast.csInf_eq
    constructor
    . simp
      use 1
      rfl
    . simp [lowerBounds]
  | k + 1 => by
    --have ih := nth_multiple_of_3_and_eq_square_sub_1_eq k
    rw [Nat.nth_eq_sInf]
    refine IsLeast.csInf_eq ?_
    constructor
    . --simp
      constructor
      . constructor
        . generalize k + 1 = k
          mod_cases k_mod_eq : k % 2 <;>
          . rw [k_mod_eq]
            simp
            ring_nf
            omega
        . use ((k + 1) / 2 * 3 + (k + 1) % 2 + 1)
      . intro k' k'_lt
        rw [nth_multiple_of_3_and_eq_square_sub_1_eq]
        suffices k' / 2 * 3 + k' % 2 + 1 < (k + 1) / 2 * 3 + (k + 1) % 2 + 1 by
          have := n_sq_ge_1 k'
          have := n_sq_ge_1 (k + 1)
          have : (k' / 2 * 3 + k' % 2 + 1) ^ 2 < ((k + 1) / 2 * 3 + (k + 1) % 2 + 1) ^ 2 := by
            gcongr --nlinarith
          omega
        set k'' := k + 1
        suffices StrictMono (fun k => k / 2 * 3 + k % 2 + 1) by
          exact this k'_lt
        refine strictMono_nat_of_lt_succ ?_
        intro k
        mod_cases k_mod_eq : k % 2
        . rw [k_mod_eq]
          simp
          change k % 2 = 0 at k_mod_eq
          have : (k + 1) % 2 = 1 := by
            omega
          rw [this]
          /-
          suffices k / 2 ≤ (k + 1) / 2 by
            linarith
           -/
          omega
        . rw [k_mod_eq]
          simp
          change k % 2 = 1 at k_mod_eq
          have : (k + 1) % 2 = 0 := by
            omega
          rw [this]
          omega
    . simp only [lowerBounds, Set.mem_setOf_eq, and_imp, forall_exists_index]
      intro m _3_dvd_m n m_eq_n_sq_sub_1 all_k'_lt_k_add_1_k'_th_lt_m
      have k_th_lt_m := all_k'_lt_k_add_1_k'_th_lt_m k (by linarith)
      rw [nth_multiple_of_3_and_eq_square_sub_1_eq] at k_th_lt_m
      have k_th_n_lt_n : k / 2 * 3 + k % 2 + 1 < n := by
        rw [m_eq_n_sq_sub_1] at k_th_lt_m
        have := n_sq_ge_1 k
        have : (k / 2 * 3 + k % 2 + 1) ^ 2 < n ^ 2 := by
          omega
        nlinarith
      suffices (k + 1) / 2 * 3 + (k + 1) % 2 + 1 ≤ n by
        rw [m_eq_n_sq_sub_1]
        have : ((k + 1) / 2 * 3 + (k + 1) % 2 + 1) ^ 2 ≤ n ^ 2 := by
          gcongr --nlinarith
        omega
      rw [m_eq_n_sq_sub_1] at _3_dvd_m
      clear m m_eq_n_sq_sub_1 all_k'_lt_k_add_1_k'_th_lt_m k_th_lt_m
      mod_cases k_mod_eq : k % 2
      . rw [k_mod_eq] at k_th_n_lt_n
        simp at k_th_n_lt_n
        set l := k / 2
        change k % 2 = 0 at k_mod_eq
        have : (k + 1) % 2 = 1 := by
          omega
        rw [this]
        have : (k + 1) / 2 = l := by
          omega
        rw [this]
        omega
      . rw [k_mod_eq] at k_th_n_lt_n
        simp at k_th_n_lt_n
        set l := k / 2
        change k % 2 = 1 at k_mod_eq
        have : (k + 1) % 2 = 0 := by
          omega
        rw [this]
        have : (k + 1) / 2 = l + 1 := by
          omega
        rw [this]
        have : n ≠ l * 3 + 3 := by
          intro n_eq
          rw [n_eq] at _3_dvd_m
          have : 3 ∣ (l * 3 + 3) ^ 2 := by
            ring_nf
            omega
          have : (l * 3 + 3) ^ 2 ≥ 1 := by
            nlinarith
          have : 3 ∣ 1 := by
            omega
          omega
        omega

theorem number_theory_640280 (k M : ℕ) (hk : 0 < k) (hM : 1 < M) :
    (Nat.nth (fun m => 3 ∣ m ∧ ∃ n, m = n^2 - 1) k) % M = (((k / 2) * 3 + k % 2 + 1)^2 - 1) % M := by
  simp [nth_multiple_of_3_and_eq_square_sub_1_eq]

end number_theory_640280
open number_theory_640280
