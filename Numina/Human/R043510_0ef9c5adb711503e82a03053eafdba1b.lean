import Mathlib

open Set Real

/-Let the set $M = \{x | x^2 - 2x - 3 < 0\}$, and the set $N = \{x | 2x < 2\}$. Find the intersection of set $M$ with the complement of set $N$ in the real numbers $R$, denoted as $M \cap \complement_R N$.-/
theorem algebra_9020 {M N : Set ℝ}
    (hM : M = {x | x ^ 2 - 2 * x - 3 < 0}) (hN : N = {x | 2 * x < 2}) :
    M ∩ (Set.compl N) = {x | 1 ≤ x ∧ x < 3} := by
    rw[hM,hN]
--We solve the inequality for M and N.compl.
--We rewrite N.compl as {a≥1}
    simp only [sub_neg, Nat.ofNat_pos, mul_lt_iff_lt_one_right,Set.compl,Set.mem_inter]
    simp only [mem_setOf_eq, not_lt]
    rw[←Set.sep_mem_eq]
    simp only [mem_setOf_eq]
--We make the set on the left hand side an explicit form {x| Prop} and prove the identity by check their elements belong to each other.
    ext x
    simp only [mem_setOf_eq, and_imp]
    rw[pow_two,←sub_mul,←one_mul 3]
    constructor
--Now we have (x - 2) * x < 3 and 1 ≤ x,we want to prove that x≤3
    rintro ⟨ine1,ine2⟩
    constructor
    linarith
--We prove that if 3<x, then (x-2)*x>3
    contrapose! ine1
    apply mul_le_mul
    repeat linarith
--On the other hand, we simply prove that (x-2)≤1 and x≤3.
    rintro ⟨ine1,ine2⟩
    simp_all only [and_true]
    apply mul_lt_mul
    repeat linarith
