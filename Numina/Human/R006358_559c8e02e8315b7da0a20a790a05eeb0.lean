import Mathlib

/-
Let $a$ be a natural number, $p$ be a prime number, and $k$ be a positive integer. Compute $a^{k(p-1)+1} \pmod p$. Show the answer is $(a \pmod p)$.
-/

theorem number_theory_636223 (a p k : ℕ) (hp: Nat.Prime p) (kpos: 0 < k):
  a^(k*(p-1)+1) ≡ a [MOD p] := by
  

  --We divide it into two cases.

  --If p ∣ a, then both numbers are 0.
  by_cases pda : p ∣ a
  have t1: a ≡ 0 [MOD p] := by exact Nat.modEq_zero_iff_dvd.mpr pda
  have t2: a^(k*(p-1)+1) ≡ 0 [MOD p] := by 
    rw [pow_succ]
    refine Nat.modEq_zero_iff_dvd.mpr ?_
    exact Dvd.dvd.mul_left pda (a ^ (k * (p - 1)))
  exact (Nat.ModEq.trans t2 t1.symm) 

  --If p ∣ a, then a and p are coprime. We apply the Fermat's little theorem.
  have acp : a.Coprime p := by 
    refine Nat.coprime_comm.mp ?_; 
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr pda
  have t1 : a ^ p.totient ≡ 1 [MOD p] := by 
    apply Nat.ModEq.pow_totient
    exact acp
  have : p.totient = p - 1 := by exact Nat.totient_prime hp
  rw [this] at t1
  have t2 : (a ^ (p - 1)) ^ k ≡ 1^k [MOD p] := by 
    exact Nat.ModEq.pow k t1
  simp at t2
  have t3 : (a ^ (p - 1)) ^ k * a ≡ 1 * a [MOD p] := by 
    exact Nat.ModEq.mul t2 rfl
  simp at t3

  rw [pow_succ]
  nth_rw 2 [mul_comm]
  rw [pow_mul]
  exact t3
  