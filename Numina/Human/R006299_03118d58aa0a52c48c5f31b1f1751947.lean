import Mathlib

/- 
Theorem: Proves the modular inverse equality (3⁻¹ + 5⁻¹)⁻¹ = 15 * 8⁻¹ in ZMod p for prime p ≠ 2, 3, 5. 
This shows the inverse of the sum of modular inverses of 3 and 5 equals 15 times the inverse of 8.
-/
theorem Number_Theory_635648 
  (p : ℕ)
  (hp : Nat.Prime p)
  (hp' : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5):
  (3⁻¹ + 5⁻¹ : ZMod p)⁻¹ = 15 * 8⁻¹ := by

  -- Step 1: Establish initial identity 5*8*3 = 15*(5+3) as algebraic starting point
  have t1: 5 * 8 * 3 = 15 * (5 + 3 : ZMod p) := by norm_num

  -- Step 2: Multiply by 5⁻¹ and apply distributive law to introduce 5⁻¹
  have t2:5⁻¹ * 5 * 8 * 3 = 15 * (5⁻¹ * 5 + 5⁻¹ * 3 : ZMod p):= by ring

  -- Step 3: Prove 5⁻¹*5=1 (since p prime ≠5, gcd(5,p)=1)
  have t2' : 5⁻¹ * 5 = (1 : ZMod p):= by 
    rw [mul_comm]
    apply ZMod.coe_mul_inv_eq_one
    refine Nat.coprime_of_dvd ?_
    intro c hc hc1 hc2
    have hc_1 : c = 1 ∨ c = 5 := by refine (Nat.dvd_prime (by trivial)).mp hc1
    have hc_2 : c = 1 ∨ c = p := by refine (Nat.dvd_prime (by trivial)).mp hc2
    have hc : c ≠ 1 := by by_contra w;simp[w] at hc;tauto
    simp [hc] at hc_1
    simp [hc , hc_1] at hc_2
    tauto
  simp [t2'] at t2

  -- Step 4: Substitute 5⁻¹*5=1 and introduce 3⁻¹ via simplification
  have t3 : 8 * 3 * 3⁻¹ = 15 * ( 1 * 3⁻¹ + 5⁻¹ * 3 * 3⁻¹ : ZMod p) := by rw[t2];ring

  -- Step 5: Prove 3⁻¹*3=1 (since p prime ≠3, gcd(3,p)=1)
  have t3' : 3⁻¹ * 3 = (1 : ZMod p) := by 
    rw [mul_comm]
    apply ZMod.coe_mul_inv_eq_one
    refine Nat.coprime_of_dvd ?_
    intro c hc hc1 hc2
    have hc_1 : c = 1 ∨ c = 3 := by refine (Nat.dvd_prime (by trivial)).mp hc1
    have hc_2: c = 1 ∨ c = p := by refine (Nat.dvd_prime (by trivial)).mp hc2
    have hc: c ≠ 1 := by by_contra w;simp[w] at hc;tauto
    simp [hc] at hc_1
    simp [hc,hc_1] at hc_2
    tauto
  rw [mul_comm] at t3'
  simp [t3',mul_assoc] at t3

  -- Step 6: Rewrite to introduce 8⁻¹ and form target structure
  have t4: 8⁻¹ * 8 = 8⁻¹ * (15 * (3⁻¹ + 5⁻¹) : ZMod p) := by rw[← t3]

  -- Step 7: Prove 8⁻¹*8=1 (since p prime ≠2, gcd(8,p)=1)
  have t4': 8⁻¹ * 8 = (1 : ZMod p) := by
    rw [mul_comm]
    apply ZMod.coe_mul_inv_eq_one
    refine Nat.coprime_of_dvd ?_
    intro c hc hc1 hc2
    have hc_2 : c = 1 ∨ c = p := by refine (Nat.dvd_prime (by trivial)).mp hc2
    cases hc_2
    case h.inl H=>simp[H] at hc;tauto
    case h.inr H=>
      simp [H] at hc1
      have t1: p ≤ 8 := by refine Nat.le_of_dvd (by trivial) hc1
      interval_cases p
      all_goals tauto
  rw [t4',← mul_assoc] at t4

  -- Step 8: Multiply by (3⁻¹+5⁻¹)⁻¹ to isolate the target expression
  have h5:((3⁻¹ + 5⁻¹) : ZMod p)⁻¹ = 8⁻¹ * 15 * (3⁻¹ + 5⁻¹) * ((3⁻¹ + 5⁻¹)⁻¹) := by 
    rw[← t4] ; ring
  rw[mul_assoc] at h5

  -- Step 9: Prove (3⁻¹+5⁻¹)*(3⁻¹+5⁻¹)⁻¹=1 (show sum is invertible)
  have h5' : ((3⁻¹ + 5⁻¹) * (3⁻¹ + 5⁻¹)⁻¹) = (1 : ZMod p) := by
    
    -- Define a as the sum of inverses for notational simplicity
    let a := ((3⁻¹ + 5⁻¹) : ZMod p)
    
    -- Assert equality of a with the sum expression (reflexive property)
    have ha : ((3⁻¹ + 5⁻¹) : ZMod p) = a := rfl
    
    -- Simplify using the definition of a
    simp [ha]
    
    -- Define b as the underlying integer value of a (for coprimality checks)
    let b := a.val
    
    -- Relate the product of b and its inverse to a * a⁻¹ using casting
    have hba : b * (b⁻¹ : ZMod p) = a * a⁻¹ := by 
    
      -- Prove (b : ZMod p) equals a by casting properties
      have r1 : (b : ZMod p) = a := by
        simp [b]
    
        -- Leverage p being prime (non-zero) to apply natural casting
        have r1 : NeZero p := by refine { out := (by exact Nat.Prime.ne_zero hp) }
        apply ZMod.natCast_zmod_val
      
      -- Rewrite the equation using the casting equality
      rw [r1]
    
    -- Rewrite to express a * a⁻¹ in terms of b's inverse
    rw [← hba]
    
    -- Apply the fundamental property of modular inverses: x * x⁻¹ = 1 when coprime
    apply ZMod.coe_mul_inv_eq_one
    
    -- Reduce to proving gcd(b, p) = 1 via contradiction
    refine Nat.coprime_of_dvd ?_
    
    -- Introduce a common divisor c of b and p
    intro c hc hc1 hc2
    
    -- Use primality of p to split cases for c (1 or p)
    have hc_2 : c = 1 ∨ c = p := by refine (Nat.dvd_prime (by trivial)).mp hc2
    
    -- Case 1: c = 1 (trivial, gcd is 1)
    cases hc_2
    case h.inl H => simp[H] at hc ; tauto
    
    -- Case 2: c = p (derive contradiction by showing p divides 8, conflicting with p ≠ 2,3,5)
    case h.inr H =>
    
      -- Substitute c = p into divisibility condition for b
      simp[H] at hc1
    
      -- Use casting equivalence to convert b ≡ 0 mod p into p | b
      have r1 : (b : ZMod p) = 0 := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd b p).mpr hc1
    
      -- Relate b's casting to the original sum expression
      have r2 : (b : ZMod p) = a := by
        simp [b]
        have r1:NeZero p:=by refine { out := (by exact Nat.Prime.ne_zero hp) }
        apply ZMod.natCast_zmod_val
    
      -- Substitute b ≡ 0 into the sum expression
      rw [r1] at r2
      simp [a] at r2
    
      -- Multiply both sides by 3 to eliminate 3⁻¹ using t3' (3⁻¹*3=1)
      have r3 : 3 * (0 : ZMod p) = (3 * 3⁻¹ + 3 * 5⁻¹) := by rw [r2] ; ring
      simp [t3'] at r3
    
      -- Multiply both sides by 5 to eliminate 5⁻¹ using t2' (5⁻¹*5=1)
      have r4 : (0 : ZMod p) * 5 = 5 + 3 * (5⁻¹ * 5) := by rw [r3] ; ring
      simp [t2'] at r4
    
      -- Normalize the ring expression to isolate p | 8
      ring_nf at r4
    
      -- Convert the modular equality 0 = 8 mod p into p divides 8
      have r5 : p ∣ 8 := by 
        exact (ZMod.natCast_zmod_eq_zero_iff_dvd 8 p).mp (id (Eq.symm r4))
    
      -- Use divisibility to bound p ≤ 8 and apply case analysis
      have t1 : p ≤ 8 := by refine Nat.le_of_dvd (by trivial) r5
    
      -- Leverage p being prime (≥2) from hp
      have t2 : p ≥ 2 := by exact Nat.Prime.two_le hp
    
      -- Contradict p ≠ 2,3,5 by eliminating other primes ≤8 (4,6,7,8 not prime)
      have t3 : p ≠ 4 := by by_contra w; simp [w] at hp ; tauto
      have t4 : p ≠ 6 := by by_contra w; simp [w] at hp; tauto
      have t5 : p ≠ 7 := by by_contra w; simp [w] at r5 ; tauto
      have t6 : p ≠ 8 := by by_contra w ; simp [w] at hp ; tauto
    
      -- Use omega tactic to resolve integer inequalities contradiction
      omega
  
  -- Simplify h5 using the proven identity (x * x⁻¹ = 1)
  simp [h5'] at h5
  
  -- Final rewrite to reorder terms and match target equality
  rw [h5, mul_comm]