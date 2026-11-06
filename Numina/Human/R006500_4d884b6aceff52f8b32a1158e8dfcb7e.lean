import Mathlib

/-
Let $M$ be a positive integer such that $M \equiv 1 \pmod 3$. Show that the remainder when the sum $\sum_{k=1}^{M} 2^{\frac{k(k+1)}{2}}$ is divided by 7 is equal to $(4 \cdot (M-1)/3 + 2) \pmod 7$.
-/

--We first have a lemma about 2^n % 7. It is prove by case analysis.
lemma l1 (n:ℕ) (npos: 0 < n):
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

--The followign three lemmas are just basic calculation.
lemma l2 (n:ℕ) (hn: 3 ≤ n): (n - 1) % 3 = 2 ↔ n ≡ 0 [MOD 3]:= by
  constructor<;> intro h

  have : 3 ∣ n-1 -2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h)); omega
  obtain ⟨k,hk⟩ := this
  refine Nat.modEq_zero_iff_dvd.mpr ?_
  use (k+1)
  omega

  refine Nat.mod_eq_of_modEq ?_ ?_
  have d3 : 3 ∣ n := by exact Nat.dvd_of_mod_eq_zero h
  obtain ⟨d,hd⟩ := d3
  have : n-1 ≡ 3 - 1 [MOD 3] := by 
    refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_); 
    use (d-1)
    omega
  simp at this
  exact this
  linarith

lemma l3 (n:ℕ) (hn: 3 ≤ n): (n - 1) % 3 = 0 ↔ n ≡ 1 [MOD 3]:= by
  constructor<;> intro h

  have : 3 ∣ n-1 := by exact Nat.dvd_of_mod_eq_zero h
  obtain ⟨k,hk⟩ := this
  refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
  use k
  omega

  refine Nat.mod_eq_of_modEq ?_ ?_
  have d3 : 3 ∣ n-1 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm h)); omega
  exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat d3)
  linarith


lemma l4 (k a b c:ℕ) (ea : Even a) (ob : Odd b) (oc : Odd c):
  Even (a + k * b + k ^ 2 * c) := by
  
  by_cases ok : Odd k
  have : Odd (k*b) := by refine Nat.odd_mul.mpr ?_; simp [ob,ok]
  have t1: Odd (a + k * b) := by exact Even.add_odd ea this
  have ok2: Odd (k^2) := by exact Odd.pow ok
  have t2: Odd (k^2 * c) := by refine Nat.odd_mul.mpr ?_; simp [ok2]; exact oc
  exact Odd.add_odd t1 t2

  have ek : Even k := by exact Nat.not_odd_iff_even.mp ok
  have t1: Even (a + k * b) := by 
    have l2 : Even (k*b) := by exact Even.mul_right ek b
    exact Even.add ea l2
  have t2 : Even (k^2 *c) := by 
    have l1 : Even (k^2) := by refine (Nat.even_pow' ?_).mpr ek; omega
    exact Even.mul_right l1 c
  exact Even.add t1 t2



theorem number_theory_637803 (M : ℕ) (Mpos: 0 < M) (hM: M ≡ 1 [MOD 3]):
  (∑ k ∈ Finset.Icc 1 M, 2 ^ (k * (k+1)/2)) % 7
  =
  (4* (M-1)/3 + 2) % 7 := by 

  --Applying the first lemma, we simplify our claim a little.
  rw [Finset.sum_nat_mod]
  have : (∑ i ∈ Finset.Icc 1 M, 2 ^ (i * (i + 1) / 2) % 7) = ∑ i ∈ Finset.Icc 1 M, 2^(((i * (i + 1) / 2)-1)%3 + 1) % 7 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp at hi
    obtain ⟨il,iu⟩ := hi
    apply l1
    simp
    nlinarith
  rw [this]
  have : 3 ∣ M - 1 := by exact (Nat.modEq_iff_dvd' Mpos).mp (id (Nat.ModEq.symm hM))
  obtain ⟨k,_⟩ := this
  have mek : M = 3*k+1 := by omega
  rw [mek]
  have : 4 * (3 * k + 1 - 1) / 3 + 2 = 4 * k + 2 := by omega
  rw [this]

  --We prove our main theorem by induction.
  have cla : ∀k:ℕ, (∑ i ∈ Finset.Icc 1 (3 * k + 1), 2 ^ ((i * (i + 1) / 2 - 1) % 3 + 1) % 7) % 7 = (4 * k + 2) % 7 := by 
    intro k
    induction' k with k hk

    simp

    have : 3*(k+1) + 1 = 3*k+4 := by omega
    rw [this]

    rw [Finset.sum_Icc_succ_top]
    rw [Finset.sum_Icc_succ_top]
    rw [Finset.sum_Icc_succ_top]
    rw [Nat.add_mod]
    nth_rw 2 [Nat.add_mod]
    nth_rw 3 [Nat.add_mod]
    rw [hk]
    simp
    
    --Now, we check these three extra terms. All are basic calculation.
    have t1 : ((3 * k + 1 + 1) * (3 * k + 1 + 1 + 1) / 2 - 1) % 3 = 2 := by 
      rw [l2]
      refine Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat ?_)
      use (3*k+2) * (k+1) / 2
      ring_nf
      have : (2 + k * 5 + k ^ 2 * 3) / 2 * 3 = (2 + k * 5 + k ^ 2 * 3)*3 /2 := by 
        refine Nat.eq_div_of_mul_eq_left ?_ ?_
        norm_num
        have : (2 + k * 5 + k ^ 2 * 3) / 2 * 3 * 2  = (2 + k * 5 + k ^ 2 * 3) / 2 * 2 * 3 := by ring
        rw [this]
        have : (2 + k * 5 + k ^ 2 * 3) / 2 * 2 = (2 + k * 5 + k ^ 2 * 3) := by 
          refine Nat.div_two_mul_two_of_even ?_
          apply l4
          use 1
          use 2; norm_num
          use 1; norm_num
        rw [this]
      rw [this]
      ring_nf
      ring_nf
      omega

    have t2 : ((3 * k + 2 + 1) * (3 * k + 2 + 1 + 1) / 2 - 1) % 3 = 2 := by 
      rw [l2]
      refine Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat ?_)
      use (k+1) * (3*k+4) / 2
      ring_nf
      have : (4 + k * 7 + k ^ 2 * 3) / 2 * 3 = (4 + k * 7 + k ^ 2 * 3)*3 /2 := by 
        refine Nat.eq_div_of_mul_eq_left ?_ ?_
        norm_num
        have : (4 + k * 7 + k ^ 2 * 3) / 2 * 3 * 2  = (4 + k * 7 + k ^ 2 * 3) / 2 * 2 * 3 := by ring
        rw [this]
        have : (4 + k * 7 + k ^ 2 * 3) / 2 * 2 = (4 + k * 7 + k ^ 2 * 3) := by 
          refine Nat.div_two_mul_two_of_even ?_
          apply l4
          use 2
          use 3; norm_num
          use 1; norm_num
        rw [this]
      rw [this]
      ring_nf
      ring_nf
      omega

    have t3 : ((3 * k + 3 + 1) * (3 * k + 3 + 1 + 1) / 2 - 1) % 3 = 0 := by 
      rw [l3]
      refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
      use (6 + k*9 + k^2*3) /2
      ring_nf
      field_simp
      have l1 : (-(1:ℤ)) + (20 + ↑k * 27 + ↑k ^ 2 * 9) / 2 = (18 + ↑k * 27 + ↑k ^ 2 * 9) / 2 := by omega
      rw [l1]
      refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ ?_ ?_
      omega
      norm_cast
      have : Even (6 + k * 9 + k ^ 2 * 3) := by 
        apply l4; 
        use 3; use 4; norm_num; use 1; norm_num

      exact even_iff_two_dvd.mp this
      norm_cast
      have : 2 * ((18 + ↑k * 27 + ↑k ^ 2 * 9) / 2) = (18 + ↑k * 27 + ↑k ^ 2 * 9) := by 
        refine Nat.two_mul_div_two_of_even ?_
        apply l4
        use 9
        use 13; norm_num
        use 4; norm_num
      rw [this]
      ring
      
      ring_nf
      omega
        
    --Pluggin the value of these three terms, we get our claim.
    rw [t1,t2,t3]
    simp
    have t4 : 4 * k + 2 + 8 + 8 + 2 =  4*k + 20 := by omega
    have t5 : 4*(k+1)+2 = 4*k+6 := by omega
    rw [t4,t5]
    exact Nat.add_mod_eq_add_mod_left (4 * k) rfl

    omega
    omega
    omega

  
  apply cla k


