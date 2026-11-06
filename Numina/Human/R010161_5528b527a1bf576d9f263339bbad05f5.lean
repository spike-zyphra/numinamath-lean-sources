import Mathlib
/-PROBLEM:Let $k=2008^2+2^2008$
 . What is the units digit of
k^2+2^k?
(A) 0(B) 2(C) 4(D) 6(E) 8-/
theorem AMC_Number_Theory_1188.lean (k:ℕ) (hk:k=2008^2+2^2008):(k^2+2^k)%10=6:=by
-- We prove that 2^n%10 is determined by n%4, for 4|n, 2^n%10=6.
  have pow2mod10 (n:ℕ) (npos:0<n):2^n%10=if n%4=0 then 6 else 2^(n%4)%10:=by
--We use induction to prove this lemma.
    induction' n,npos using Nat.le_induction with n npos hn
    simp only [Nat.succ_eq_add_one, zero_add, pow_one, Nat.reduceMod, Nat.one_mod, one_ne_zero,↓reduceIte]
    rw[Nat.pow_add_one,Nat.mul_mod]
    have nmodle:n%4<4:=by apply Nat.mod_lt;decide
--We study each case of n%4
    interval_cases p:n%4
    simp only [↓reduceIte] at hn
    rw[hn]
    simp only [Nat.reduceMod, Nat.reduceMul]
--We split the goal as it depends on (n+1)%4
    split
    rename_i h
    rw[Nat.add_mod,p] at h
    simp at h
    rw[Nat.add_mod,p]
    simp
    all_goals
--As n%4 ≠ 0, we can simplify hn.
      replace hn:2^n%10=2^(n%4)%10:=by
        rw[hn,p]
        simp
      split
      rename_i hi
      rw[Nat.add_mod,Nat.one_mod,p] at hi
      simp at hi
      rw[hn]
    rw[Nat.add_mod,Nat.one_mod,p];simp
    rw[Nat.add_mod,Nat.one_mod,p];simp;
    rw[p];simp
    rename_i hn
    rw[Nat.add_mod,p] at hn
    simp only [Nat.one_mod, Nat.reduceAdd, Nat.mod_self, not_true_eq_false] at hn
--Now we compute k%4 and k%10 as this is used in the addition.
  have kmod:k%4=0 ∧ k%10=0:=by
    rw[hk]
    norm_num
  rw[Nat.add_mod,Nat.pow_mod]
  have :2^k%10=6:=by
    rw[pow2mod10,kmod.1]
    simp only [↓reduceIte];linarith
--Substitue this and kmod to get the desired identity.
  rw[this,kmod.2]