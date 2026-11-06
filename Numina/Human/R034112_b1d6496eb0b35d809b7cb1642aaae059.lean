import Mathlib 

/-Find all prime positive integers $p, q$ such that $2 p^{3}-q^{2}=2(p+q)^{2}$.-/
theorem AIME_Algebra_13680 : {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ (2 : ℝ)*p^3 - q^2 = 2*(p+q)^2} = {(3,2)} := by 
  ext ⟨p, q⟩ 
  simp 
  constructor
  · intro ⟨hp, hq, h1⟩
    --  The given equation can be rewritten as $2 p^{2}(p-1)=q(3 q+4 p)$.
    have h2 : (2 : ℝ)* p^2 * (p - 1) = q * (3 * q + 4 * p) := by    
      linarith only [h1]
    have : 1 < p := hp.one_lt
    have : 1 < q := hq.one_lt
    have h2 : 2* p^2 * (p - 1) = q * (3 * q + 4 * p) := by 
      convert h2 using 1
      norm_cast
      rw [Int.subNatNat_eq_coe, ←Nat.cast_sub]
      norm_cast
      linarith
    -- Hence $p\left|3 q^{2}+4 p q \Rightarrow p\right| 3 q^{2} 
    have : p ∣ q^2 * 3 := by 
      have : p ∣ 2 * p ^ 2 * (p - 1) := ⟨2*p*(p-1), by ring⟩
      have : p ∣ q * (3*q + 4*p) := by rwa [<-h2]
      ring_nf at this
      exact (Nat.dvd_add_right ⟨4*q, by ring⟩).1 this
    rcases (Nat.Prime.dvd_mul hp).1 this with hl | hr
    · -- If $p \mid q$, then $p=q$. The equation becomes $2 p^{3}-9 p^{2}=0$ which has no prime solution.
      have pdvdq : p ∣ q := Nat.Prime.dvd_of_dvd_pow hp hl
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 pdvdq
      simp [this] at h1
      have c1 : (q^2 : ℝ) * (2 * q - 9) = 0 := by linarith
      have : (q : ℝ) ≠ 0 := by norm_cast; omega
      have c2 : 2 * q - (9:ℝ) = 0 := 
        eq_zero_of_ne_zero_of_mul_left_eq_zero (by norm_cast at this ⊢; simp [this]) c1
      have : 2 * q - 9 = 0 := by 
        norm_cast at c2
        by_cases q5 : q ≤ 5 
        · interval_cases q <;> norm_num at c1
        · push_neg at q5
          rw [Int.subNatNat_eq_coe, ←Nat.cast_sub, Nat.cast_eq_zero] at c2 
          exact c2
          linarith
      exfalso 
      by_cases q5 : q ≤ 5 
      · interval_cases q <;> norm_num at c1
      · push_neg at q5
        have : 0 < 2 * q - 9 := by omega 
        linarith
    · -- If $p \mid 3$, then $p=3$. The equation becomes $q^{2}+4 q-12=0 \Leftrightarrow(q-2)(q+6)=0$.
      have p3:= (Nat.Prime.dvd_iff_eq Nat.prime_three (Nat.Prime.ne_one hp)).1 hr
      simp [←p3] at h2
    -- Since $q>0$, we get $q=2$, so we have the solution $(p, q)=(3,2)$.
      have : 2 ≤ q := Nat.Prime.two_le hq 
      have : q ≤ 2 := by 
        by_contra! hc
        have : 2 * (3 * 2 + 12) < q * (3 * q + 12) := by 
          apply mul_lt_mul_of_pos'
          · omega
          · norm_num; omega
          any_goals positivity
        linarith
      exact ⟨p3.symm, by omega⟩ 
  · intro ⟨hp, hq⟩  
    simp [hp, hq, Nat.prime_three, Nat.prime_two]
    norm_num