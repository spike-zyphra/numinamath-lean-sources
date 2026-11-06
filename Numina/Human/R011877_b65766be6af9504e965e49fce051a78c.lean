import Mathlib

/-Find all integer pairs $(a, b)$, where $a \geqslant 1, b \geqslant 1$, and satisfy the equation $a^{b^{2}}=b^{a}$.

In summary, all positive integer pairs that satisfy the equation are
$$
(a, b)=(1,1),(16,2),(27,3) .
$$-/
theorem number_theory_298793 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a^(b^2) = b^a ↔ (a = 1 ∧ b = 1) ∨ (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3) := by 
    constructor
    intro hab
    -- Obviously, when $a, b$ have one equal to 1, $(a, b)=(1, 1)$. Now assume $a, b \geqslant 2$.
    by_cases h1 : a = 1 ∨ b = 1
    · rcases h1 with h1 |h1
      <;> simp [h1] at hab
      <;> simp [h1,hab]
    simp at h1
    -- Let $t=\frac{b^{2}}{a}$, then from the equation in the problem we get $b=a^{t}, a t=a^{2 t}$, thus $t=a^{2 t-1}$. 
    let t : ℝ := b ^ 2 / a
    have ht1 : b = (↑a:ℝ) ^ t := by
      simp [t]
      ring_nf
      rw [Real.rpow_mul (by simp)]
      refine (Real.eq_rpow_inv (by simp) ?_ (by simp ;linarith)).mpr ?_
      apply Real.rpow_nonneg
      simp
      rify at hab
      simp [pow_two,Real.rpow_mul]
      rw [← hab,pow_two,pow_mul]
    have ht2 : a * t = a ^ (2 * t) := by
      rw [mul_comm 2,Real.rpow_mul (by simp),← ht1]
      simp [t]
      rw [mul_comm]
      apply div_mul_cancel₀
      simp ;linarith
    have ht3 : t = a ^ (2 * t - 1) := by
      rw [Real.rpow_sub,← ht2,Real.rpow_one,mul_comm]
      rw [mul_div_cancel_right₀]
      simp ;linarith ;simp ;linarith
    -- Therefore, $t&gt;0$. 
    have ht4 : 0 < t := by
      rw [ht3]
      refine Real.rpow_pos_of_pos (by simp ;linarith) (2 * t - 1)
    -- If $2 t-1 \geqslant 1$, then $t=a^{2 t-1} \geqslant(1+1)^{2 t-1} \geqslant 1+(2 t-1)=2 t&gt;t$, which is a contradiction. 
    by_cases h2 : 1 ≤ 2 * t - 1
    · have h3 : 2 ^ (2 * t - 1) ≤ t := by
        nth_rewrite 2 [ht3]
        refine (Real.rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
        simp ;linarith
        linarith
        simp ;omega
      have h4 : 1 + (2 * t - 1) * 1 ≤ (1 + 1) ^ (2 * t - 1) := by
        apply one_add_mul_self_le_rpow_one_add
        simp ;linarith
      norm_num at h4
      linarith
    -- So $2 t-1&lt;1$ and $t$ is a rational number.
    push_neg at h2
    -- From $a=b^{k}$ we have $$ k=b^{k-2} \text{.} $$
    -- If $k \leqslant 2$, then $k=b^{k-2} \leqslant 1$, which contradicts the previously proven $k&gt;1$, so $k&gt;2$.
    let k := 1 / t
    have hk1 : a = (↑b :ℝ) ^ k := by
      simp [k,ht1]
      rw [← Real.rpow_mul (by simp),mul_inv_cancel₀,Real.rpow_one]
      simp ;linarith
    have hk2 : k = b ^ (k - 2) := by
      rw [Real.rpow_sub,← hk1]
      simp [k,t]
      simp ;linarith
    by_cases hk3 : k ≤ 2
    · have : k ≤ 1 := by
        rw [hk2]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        simp ;linarith ;linarith
      have : 1 < k := by
        simp only [k]
        refine one_lt_one_div ht4 ?_
        linarith
      linarith
    push_neg at hk3
    -- Let $k=\frac{p}{q}, p, q \in \mathbb{N}, (p, q)=1$, then $p&gt;2q$. 
    have hkpq : ∃ p q : ℕ , k = p / q  ∧ Nat.Coprime p q := by
      have : ∃ s : ℚ , s > 0 ∧ s = k := by
        use (a / b ^ 2)
        simp [k,t]
        refine div_pos ?_ ?_
        simp ;linarith
        refine sq_pos_of_pos ?_ ;simp ;linarith
      rcases this with ⟨s,hs1,hs2⟩
      use s.num.natAbs, s.den
      rw [← hs2]
      constructor
      · have : s = s.num / s.den := by
          exact Eq.symm (Rat.num_div_den s)
        nth_rewrite 1 [this]
        simp
        apply (div_left_inj' ?_).mpr
        have : s.num = s.num.natAbs := by
          refine Int.eq_natAbs_of_zero_le ?_
          refine Rat.num_nonneg.mpr ?_
          linarith
        nth_rewrite 1 [this]
        exact rfl
        simp
      exact s.reduced
    rcases hkpq with ⟨p,q,hk4,hpq⟩
    have hpq2 : p > 2 * q := by
      rw [hk4] at hk3
      rify
      have : 0 < q := by
        refine Nat.pos_of_ne_zero ?_
        by_contra!
        simp [this] at hk3
        linarith
      apply (lt_div_iff₀ (by simp;exact this)).mp at hk3 
      exact hk3
    -- Thus, from (1) we get $$ \left(\frac{p}{q}\right)^{q}=k^{q}=b^{p-2q} \in \mathbb{Z}. $$
    have hz : ∃ m : ℕ , m = k ^ q := by
      use (b^(p-2*q))
      rw [hk2,hk4]
      simp
      have : ((↑b:ℝ) ^ (↑p / ↑q - 2 : ℝ)) ^ q = ((↑b:ℝ) ^ (↑p / ↑q - 2 : ℝ)) ^ (q:ℝ) := by
        rw [Real.rpow_natCast]
      rw [this,← Real.rpow_mul (by simp),sub_mul,
      ← Real.rpow_natCast,Nat.cast_sub,div_mul_cancel₀,Nat.cast_mul]
      simp ;simp
      by_contra!
      simp [this] at hk4
      linarith ;linarith
    -- This implies $q^{q} \mid p^{q}$. But $p, q$ are coprime, so $q=1$, meaning $k$ is a natural number greater than 2. 
    rcases hz with ⟨m,hm⟩ 
    have hq1 : q = 1 := by
      have : m * q ^ q = p ^ q := by
        rify
        rw [hm,hk4,← mul_pow,div_mul_cancel₀]
        simp
        by_contra!
        simp [this] at hk4
        linarith
      have : q ^ q ∣ p ^ q := by
        use m ;rw [← this] ;ring_nf
      apply (Nat.pow_dvd_pow_iff 
      (by by_contra! ;simp [this] at hk4 ;linarith)).mp 
      at this
      refine Nat.Coprime.eq_one_of_dvd ?_ this
      exact Nat.coprime_comm.mp hpq
    have hk5 : ∃ K : ℕ, 2 < K ∧ k = K := by
      use p
      simp [hq1] at hpq2 hk4 
      simp [hk4,hpq2]
    rcases hk5 with ⟨K,hK1,hK2⟩
    -- When $b=2$, from (1) we get $k=2^{k-2}$, so $k \geqslant 4$. 
    by_cases hb1 : b = 2
    · rw [hb1] at hk2
      have hK3 : 2 ^ (K - 2) = K := by
        rify
        rw [← hK2,hk2,hK2,← Real.rpow_natCast,Nat.cast_sub]
        simp ;linarith
      -- Also, $$ \begin{array}{l} k=2^{k-2} \geqslant C_{k-2}^{0}+C_{k-2}^{1}+C_{k-2}^{2} \ =1+(k-2)+\frac{(k-2)(k-3)}{2} \ =1+\frac{(k-1)(k-2)}{2} \geqslant 1+(k-1)=k, \end{array} $$
      -- equality holds if and only if $k=4$,
      have hK4 : K = 4 := by
        by_cases hK5 : K > 4
        · have : 2 ^ (K - 2 - 1 ) * 2 ^ 1 > (1 + (K - 2 - 1)) * 2 ^ 1 := by
            have : ∀ n > 1 , n + 1 < 2 ^ n := by
              intro n
              induction n with
              | zero => simp
              | succ n ih =>
                intro hn
                by_cases hn' : n > 1
                · have := ih hn'
                  rw [pow_add,pow_one,mul_two]
                  have : 1 < 2 ^ n := by
                    exact Nat.lt_trans hn (ih hn')
                  linarith
                simp at hn'
                interval_cases n
                simp at hn
                norm_num
            specialize this (K - 2 - 1) (by omega)
            omega
          rw [← pow_add,add_comm 1,Nat.sub_add_cancel,pow_one] at this
          have : (K - 2) * 2 > K := by
            omega
          linarith ;omega
        simp at hK5
        -- so, $$ \begin{array}{l} a=b^{k}=2^{4}=16. 
        interval_cases K
        norm_num at hK3
        rfl
      simp [hb1]
      simp [hK2,hK4,hb1] at hk1
      norm_num at hk1
      rify ;exact hk1
    -- \text{When } b \geqslant 3, \ k=b^{k-2} \geqslant(1+2)^{k-2} \geqslant 1+2(k-2) \ \quad=2 k-3. \end{array} $$
    -- Thus, $k \leqslant 3$. This implies $k=3$. Therefore,
    by_cases hb2 : 3 ≤ b
    · have hb3 : (1 + 2) ^ (k - 2) ≤ k := by
        nth_rewrite 2 [hk2]
        refine Real.rpow_le_rpow ?_ ?_ ?_
        norm_num ;norm_num ;exact hb2
        rw [hK2] ;simp ;linarith
      have hb4 : 1 + (k - 2) * 2 ≤ (1 + 2) ^ (k - 2) := by
        apply one_add_mul_self_le_rpow_one_add
        norm_num ;rw [hK2]
        apply le_sub_iff_add_le.mpr
        norm_num ;linarith
      have : 1 + (k - 2) * 2 ≤ k := by linarith
      have : k ≤ 3 := by linarith
      simp [hK2] at this
      interval_cases K
      simp [hK2] at hk2
      norm_num at hk2
      simp [hK2,← hk2] at hk1
      norm_num at hk1
      right ;right ;rify ;simp [hk1,hk2]
    simp at hb2
    interval_cases b
    simp at hk2
    simp [hk2] at hk3
    norm_num at hb1
    
    
    intro hab
    rcases hab with h1 |h1 |h1
    <;> simp [h1]

      
    
        
        
        
        
      
      



      


    