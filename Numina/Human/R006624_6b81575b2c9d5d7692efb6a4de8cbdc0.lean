import Mathlib

theorem number_theory_639356 (n:ℕ) (npos: 0 < n):
  2^n % 7 = 2^((n-1)%3 + 1) % 7 := by

  --We divide the proof into 3 cases according to the remainder of n divided by 3. All are simple calculation.

  --Case 1 : n is divible by 3.
  by_cases m0 : n % 3 = 0
  have : 3 ∣ n := by exact Nat.dvd_of_mod_eq_zero m0
  obtain ⟨k,hk⟩ := this
  rw [hk]
  have : (3 * k - 1) % 3 = 2 := by 
    refine Nat.mod_eq_of_modEq ?_ ?_
    have : 3 * k ≡ 3 [MOD 3] := by 
      exact Nat.ModEq.trans (congrFun (congrArg HMod.hMod (id (Eq.symm hk))) 3) m0
    have : 3 * k - 1 ≡ 3 - 1 [MOD 3] := by 
      refine Nat.ModEq.symm ((fun {n a b} h => (Nat.modEq_iff_dvd' h).mpr) ?_ ?_)
      omega
      use (k-1)
      omega
    simp at this
    exact this
    linarith
  rw [this]
  rw [pow_mul]
  ring_nf
  rw [Nat.pow_mod]
  ring_nf
  
  --Case 2 : The remainder of n divided by 3 is 1.
  by_cases m1 : n % 3 = 1
  have : 3 ∣ n-1 := by exact (Nat.modEq_iff_dvd' npos).mp (id (Eq.symm m1))
  obtain ⟨k,hk⟩ := this
  rw [hk]
  have : n = 3*k+1 := by omega
  rw [this]
  have : (3 * k) % 3 = 0 := by 
    exact Nat.mul_mod_right 3 k
  simp [this]
  rw [pow_succ, pow_mul]
  ring_nf
  rw [Nat.mul_mod, Nat.pow_mod]
  ring_nf
  
  --Case 3 : The rest is 2 modulo 3.
  have m2 : n % 3 = 2 := by omega
  have : 3 ∣ n-2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm m2)); omega
  obtain ⟨k,hk⟩ := this
  have e1 : n = 3*k + 2 := by omega
  rw [e1]
  have : (3 * k +2 - 1) % 3 = 1 := by 
    field_simp
    refine Nat.mod_eq_of_modEq ?_ ?_
    have : 3 * k ≡ 0 [MOD 3] := by 
      refine Nat.modEq_zero_iff_dvd.mpr ?_
      use k
    have : 3 * k + 1 ≡ 0 + 1 [MOD 3] := by 
      exact Nat.ModEq.add_right 1 this
    simp at this
    exact this
    linarith
  rw [this]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_mul]
  rw [Nat.mul_mod]
  nth_rw 2 [Nat.mul_mod]
  rw [Nat.pow_mod]
  ring_nf

