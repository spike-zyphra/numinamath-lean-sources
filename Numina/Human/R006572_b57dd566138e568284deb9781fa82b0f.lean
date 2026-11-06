import Mathlib

/-
For natural numbers r, k, n and m, where:
- k ≥ n
- m is the multiplicative order of 5 modulo 2^n and r ≡ k - n modulo m
Then: 5^k ≡ (the value of 5^r modulo 2^n) * 5^n modulo 10^n
-/
theorem five_power_congruence
  (r:ℕ)
  (h_1:k ≥ n)
  (h_2:m = orderOf (5 : ZMod (2^n)))
  (h_3:r≡k-n [ZMOD m]):
  5^k ≡ (((5^r) :ZMod (2^n)).val) * 5^n [ZMOD 10^n]:=
by
  let t:=(((5^r) :ZMod (2^n)).val)
  have ht:(((5^r) :ZMod (2^n)).val)=t :=rfl
  simp[ht]
  norm_cast
  apply Int.natCast_modEq_iff.mpr
  -- Express 10^n as 5^n * 2^n
  have h1:10 ^ n=5^n * 2^n :=by
    rw[← mul_pow]
    simp
  rw[h1]
  -- Commute multiplication
  have h2:t*5^n=5^n *t:=by apply mul_comm
  rw[h2]
  -- Factor 5^k as 5^n * 5^{k-n}
  have h3:5^k=5^n * 5^(k-n):=by
    rw[← pow_add]
    simp
    omega
  rw[h3]
  -- 5^n is nonzero
  have h4:5^n≠0 :=by exact Ne.symm (NeZero.ne' (5 ^ n))
  apply (Nat.ModEq.mul_left_cancel_iff' h4).mpr
  apply Int.natCast_modEq_iff.mp
  simp only [t]

  -- Lemma: Integer values in ZMod are congruent to their representatives
  have R_mod(p:ℤ):(p:ZMod (2^n)).val≡p [ZMOD (2^n)]:=by
    let r := (p : ZMod (2^n)).val
    have h : (p : ZMod (2^n)).val = r := by
      unfold r
      simp [ZMod.val_intCast]
    rw [h]
    apply Int.modEq_iff_dvd.2
    have h_mod : p % (2^n) = r := by
      rw [ZMod.val_intCast]
      norm_cast
    rw [← h_mod]
    rw [← Int.neg_sub]
    apply Int.dvd_neg.mpr
    norm_cast
    exact Int.dvd_emod_sub_self

  -- Apply lemma to 5^r
  have h5:(5 ^ r:ZMod (2^n)).val ≡ 5^r [ZMOD (2^n)] :=by
    let R:=R_mod ((5^r) :ℤ )
    simp at R
    simp --get (5 ^ r).cast ≡ 5 ^ r [ZMOD 2 ^ n]
    tauto
  simp at h5
  simp

  -- Main congruence proof: 5^r ≡ 5^{k-n} mod 2^n
  have h6:5^r ≡ 5^(k-n) [ZMOD (2^n)]:=by
    -- Prove that 5^m ≡ 1 mod 2^n (order property)
    have t1:((5^m):ZMod (2^n))=1:=by
      simp[h_2]
      exact pow_orderOf_eq_one 5

    -- Prove that 5^r = 5^{k-n} in ZMod(2^n)
    have h_eq : (5 ^ r : ZMod (2 ^ n)) = (5 ^ (k - n) : ZMod (2 ^ n)) := by
      -- Show exponents are congruent mod m in ZMod
      have h_exp : (r : ZMod m) = ((k - n): ZMod m) := by
        norm_cast
        rw [ZMod.natCast_eq_natCast_iff']
        norm_cast at h_3
        exact Eq.symm ((fun {m n} => Int.ofNat_inj.mp) (id (Int.ModEq.symm h_3)))
      norm_cast at h_exp

      -- Convert to natural number congruence
      have h_nat_mod : r ≡ k - n [MOD m] := by
        rw [Nat.ModEq]
        rw [ZMod.natCast_eq_natCast_iff'] at h_exp
        exact h_exp

      -- Get modulus equality
      have h_mod : r % m = (k - n) % m := by
        rw [ZMod.natCast_eq_natCast_iff'] at h_exp
        exact h_exp

      -- Apply modulus congruence
      have h_mod':r ≡ (k-n) [MOD m]:=by exact h_mod
      rw [h_2] at h_mod'

      -- Step-by-step proof using modulus reduction
      -- Reduce exponents modulo order
      have m1: (5 : ZMod (2^n)) ^ r = (5 : ZMod (2^n)) ^ (r % m) := by
        symm
        exact Eq.symm (pow_eq_pow_mod r t1)
      rw [m1]

      have m2: (5 : ZMod (2^n)) ^ (k - n) = (5 : ZMod (2^n)) ^ ((k - n) % m) := by
        symm
        exact Eq.symm (pow_eq_pow_mod (k - n) t1)
      rw [m2]

      -- Congruence of reduced exponents
      congr 1

    -- Convert ZMod equality to natural number congruence
    norm_cast at h_eq
    have t2:5 ^ r ≡ 5 ^ (k - n) [MOD 2 ^ n]:=by
      apply (ZMod.eq_iff_modEq_nat (2^n)).mp h_eq

    -- Convert to integer congruence
    have t3:((5:ℤ)^r:ZMod (2^n))=((5:ℤ)^(k-n):ZMod (2^n)):=by
      simp
      simp at h_eq
      exact h_eq

    -- Prove divisibility for integer congruence
    refine Int.modEq_of_dvd ?_
    have t4:(((5:ℤ)^(k-n)-(5:ℤ)^(r)):ZMod (2^n))=0:=by
      exact sub_eq_zero_of_eq (id (Eq.symm t3))
    norm_cast at t4
    norm_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Int.subNatNat (5 ^ (k - n)) (5 ^ r)) (2 ^ n)).mp t4

  -- Combine both congruence results
  exact Int.ModEq.trans (id (Int.ModEq.symm h6)) (id (Int.ModEq.symm h5))
