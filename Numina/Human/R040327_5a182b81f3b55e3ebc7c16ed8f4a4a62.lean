import Mathlib

def isGood (n : ℕ) := ∃ p, (Nat.Prime p ∧ (∃ m, n = p + m^2))

/- Example 13 If a perfect square can be written as the sum of a prime number and another perfect square, it is called a "good square number". If a perfect square cannot be written as the sum of a prime number and another perfect square, it is called a "bad square number". Prove that there are infinitely many good square numbers and infinitely many bad square numbers. -/
theorem number_theory_302215 :
    {n | IsSquare n ∧ isGood n}.Infinite ∧
    {n | IsSquare n ∧ ¬isGood n}.Infinite := by

    --The first claim.
    --We prove that (p+1)/2^2 is good, since it equals $p+((1+(p-1)/2)^2$.
    --Then we use the fact that there are infinite odd primes.
    constructor
    let S := {p:ℕ  | Nat.Prime p ∧ Odd p}
    let T := {n:ℕ | IsSquare n ∧ isGood n}
    let f: ℕ→ ℕ := fun p ↦ ((p+1)/2)^2
    have fima: (f '' S) ⊆ T := by 
      simp [f, S, T]
      intro p pp oddp
      have evenpp1 : Even (p + 1) := by exact Odd.add_one oddp
      have pge3 : 3 ≤ p := by 
        have : 2 ≤ p := by exact Nat.Prime.two_le pp
        by_contra
        have pe2 : p = 2 := by linarith
        rw [pe2] at oddp
        obtain ⟨r,hr⟩ := oddp
        omega
      constructor
      
      obtain ⟨k, hk⟩ := evenpp1
      use k; simp [hk]
      ring_nf
      field_simp

      unfold isGood
      use p
      simp [pp]
      use ((p-1)/2)
      have evenpm1 : Even (p-1) := by refine Odd.tsub_odd oddp ?_; norm_num
      obtain ⟨k, hk⟩ := evenpm1
      have tmp1: p+1 = k+k+2 := by omega
      have tmp2: p = k+k+1 := by omega
      rw [hk,tmp1,tmp2]
      field_simp
      have : (k + k) / 2 = k := by omega
      rw [this]
      ring

    have injf: Set.InjOn f S := by  
      simp [f, S]
      unfold Set.InjOn
      intro x1 hx1 x2 hx2 heq
      obtain ⟨hx11,hx12⟩:= hx1
      obtain ⟨hx21,hx22⟩:= hx2
      have : 2 ≤ x1 := by exact Nat.Prime.two_le hx11
      have : 2 ≤ x2 := by exact Nat.Prime.two_le hx21
      have evenx1p1: Even (x1 + 1) := by exact Odd.add_one hx12
      have evenx2p1: Even (x2 + 1) := by exact Odd.add_one hx22
      simp at heq
      
      have eq: (x1 + 1) / 2  * 2 = (x2 + 1) / 2  * 2 := by linarith
      have t1 : (x1 + 1) / 2  * 2  = x1 + 1 := by 
        refine Nat.div_two_mul_two_of_even ?_
        exact evenx1p1
      have t2 : (x2 + 1) / 2  * 2  = x2 + 1 := by 
        refine Nat.div_two_mul_two_of_even ?_
        exact evenx2p1
      rw [t1,t2] at eq
      linarith
              
    have Sinf: S.Infinite := by 
      simp [S]
      refine Set.infinite_of_forall_exists_gt ?_
      intro a
      have : {p:ℕ | Nat.Prime p}.Infinite := by exact Nat.infinite_setOf_prime
      rw [Set.infinite_iff_exists_gt] at this
      specialize this (a+10)
      obtain ⟨b,hb⟩ := this
      simp at hb ⊢
      obtain ⟨hb1,hb2⟩ := hb
      use b
      simp [hb1]
      constructor
      by_contra noddb
      have evenb : Even b := by exact Nat.not_odd_iff_even.mp noddb
      have : b = 2 := by exact (Nat.Prime.even_iff hb1).mp evenb
      rw [this] at hb2
      linarith
      linarith

    
    have Tinf : T.Infinite := by
      have : (f '' S).Infinite := by 
        apply Set.Infinite.image
        exact injf
        exact Sinf
      exact Set.Infinite.mono fima this
    
    simp [T] at Tinf
    exact Tinf
    

    --The second claim.
    --We prove that (3n+2)^2 is a bad square.
    let S := {n:ℕ  | 1 ≤ n}
    let T := {n:ℕ | IsSquare n ∧ ¬isGood n}
    let f: ℕ→ ℕ := fun n ↦ (3*n+2)^2
    have fima: (f '' S) ⊆ T := by 
      simp [S,T]
      
      intro n nge1
      constructor
      simp [f]
      use 3*n+2
      ring
      
      --We prove that (3*n+2)^2 is not good
      --If it is good, then (3n+2+x)(3n+2-x) = p
      --This a a contradiction to the fact that p is a prime.
      by_contra ifisgood
      unfold isGood at ifisgood
      obtain ⟨p, hp⟩ := ifisgood
      obtain ⟨pp, exix⟩ := hp
      obtain ⟨x, h⟩ := exix
      simp [f] at h
      have peq: p = (3*n+2)^2 - x^2 := by omega
      have : 2 ≤ p := by exact Nat.Prime.two_le pp
      have : 0 < x := by 
        by_contra npos
        have xe0 : x= 0 := by omega
        rw [xe0] at h
        field_simp at h
        have : 3*n+2 ∣ p := by use 3*n+2; nlinarith
        have : 3*n+2 = 1 ∨ 3*n+2 = p := by exact (Nat.dvd_prime pp).mp this
        exfalso
        rcases this with h1|h3n2p
        omega
        rw [h3n2p] at h
        nlinarith

      have : x < 3*n + 2 := by nlinarith
      have : 2 ≤ (3*n+2)^2 - x^2 := by linarith
      have eqp: (3*n+2+x)*(3*n+2-x) = p := by 
        have t: (3*(n:ℤ)+2+x)*(3*n+2-x) = (3*n+2)^2 - x^2 := by ring
        have : (3*n+2+x)*(3*n+2-x) = (3*n+2)^2 - x^2 := by 
          zify
          have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (3 * n + 2 - x) = 3*(n:ℤ)+2-x := by omega
          rw [this]
          rw [t]
          nlinarith

          
        rw [this];
        symm
        exact peq
      have : 3*n+2-x < 3*n+2+x := by omega
      have myd: (3*n+2+x) ∣ p := by
        use (3*n+2-x)
        symm
        assumption
      have : (3*n+2+x) = 1 ∨ (3*n+2+x) = p := by exact (Nat.dvd_prime pp).mp myd
      rcases this with eq | eq
      rw [eq] at eqp
      field_simp at eqp
      linarith
      rw [eq] at eqp
      have eq2 : 3 * n + 2 -x = 1 := by nlinarith
      have : p = 3*(2*n+1) := by nlinarith
      have : 3 ∣ p := by use (2*n+1)
      have : 3 = 1 ∨ 3 = p := by exact (Nat.dvd_prime pp).mp this
      simp at this
      omega

    have injf: Set.InjOn f S := by 
      unfold Set.InjOn
      intro x1 hx1 y1 hy1 hf
      simp [f] at hf
      exact hf
    have Sinf: S.Infinite := by 
      simp [S]
      refine Set.infinite_of_forall_exists_gt ?_
      intro a
      use max 1 (a+1)
      simp
    
    have Tinf : T.Infinite := by
      have : (f '' S).Infinite := by 
        apply Set.Infinite.image
        exact injf
        exact Sinf
      exact Set.Infinite.mono fima this
    
    simp [T] at Tinf
    exact Tinf
    
    