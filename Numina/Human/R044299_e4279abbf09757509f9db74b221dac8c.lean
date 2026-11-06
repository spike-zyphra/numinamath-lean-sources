import Mathlib

/- Let $\mathbb{Z}^{+}$be the set of positive integers.
 Determine all functions $f: \mathbb{Z}^{+} \rightarrow \mathbb{Z}^{+}$ such that $a^{2}+f(a) f(b)$ is divisible by $f(a)+b$ for all positive integers $a$ and $b$.
Answer: The answer is $f(n)=n$ for all positive integers $n$.
Clearly, $f(n)=n$ for all $n \in \mathbb{Z}^{+}$satisfies the original relation. 
We show some possible approaches to prove that this is the only possible function. -/

theorem number_theory_605968 {f: ℤ → ℤ} (hf: ∀ n, 0 < n → 0 < f n): 
  (∀ a b, 0 < a ∧ 0 < b → (f a + b) ∣ a ^ 2 + f a * f b) ↔ ∀ n, 0 < n → f n = n := by

  constructor
  
  -- the forward direction: show that f(n) = n
  . 
    intro h
    intro t ht
    have ft:= hf t ht
    -- show f 1 = 1
    have f1: f 1 = 1 := by
      specialize h 1 1
      norm_num at h
      specialize hf 1
      norm_num at hf
      set a:= f 1
      have o: a + 1 ∣ a - 1 := by
        rw [show a - 1 = a * (a + 1) - (1 + a * a) by ring]
        apply dvd_sub
        simp
        exact h
      by_contra! s
      have u: 0 < a - 1 := by omega
      apply exists_eq_mul_right_of_dvd at o
      obtain ⟨k, hk⟩ := o
      have v: 0 < a + 1 := by omega
      have ok: 0 < k := by nlinarith
      replace ok: 1 ≤ k := by omega
      nlinarith
    
    -- show ∀ b, b ≤ f b
    have l: ∀ b, 0 < b → b ≤ f b := by
      intro b hb
      specialize h 1 b
      norm_num at h
      simp [hb, f1] at h
      apply exists_eq_mul_right_of_dvd at h
      obtain ⟨k, hk⟩ := h
      specialize hf b hb
      have ok: 0 < k := by nlinarith
      nlinarith
      
    -- show ∀ a, 2 ≤ a → f a ≤ a ^ 2 - 2
    have u: ∀ a, 2 ≤ a → f a ≤ a ^ 2 - 2 := by
      intro a ha
      specialize h a 1 
      have o: 0 < a := by omega
      simp [o, f1] at h
      have r: f a + 1 ∣ a ^ 2 - 1 := by
        rw [show a ^ 2 - 1 = a ^ 2 + f a - (f a + 1) by ring]
        apply dvd_sub
        exact h
        simp
      apply exists_eq_mul_right_of_dvd at r
      obtain ⟨k, hk⟩ := r
      specialize hf a o
      have ok: 0 < k := by nlinarith
      nlinarith
    
    -- then we take a sufficiently large prime
    have hp:= Nat.exists_infinite_primes (t * f t + 3).natAbs
    obtain ⟨p, lp, pp⟩ := hp
    zify at lp
    have eq: |t * f t + 3| = t * f t + 3 := by
      apply abs_of_nonneg
      nlinarith
    rw [eq] at lp
    clear eq
    have lfp:= hf p
    have rp: 0 < (p: ℤ) := by nlinarith
    simp [rp] at lfp

    -- then we show that p is odd
    have op: Odd (p: ℤ) := by
      simp
      apply Nat.Prime.odd_of_ne_two
      exact pp
      by_contra! s
      simp [s] at lp
      nlinarith
     
    -- then we show that f p = p
    have fp: f p = p := by
      specialize h p (f p)
      simp [rp, lfp] at h
      replace h: f ↑p ∣ ↑p ^ 2 + f ↑p * f (f ↑p) := by
        have o1: f ↑p ∣ f p + f p := by
          simp
        apply dvd_trans o1 h
      have v: f p ∣ p ^ 2 := by
        rw [show p ^ 2 = p ^ 2 + f ↑p * f (f ↑p) - f ↑p * f (f ↑p) by ring]
        apply dvd_sub
        exact h
        simp
      rw [← Int.natAbs_dvd_natAbs] at v
      rw [Int.natAbs_pow] at v
      simp at v
      rw [Nat.dvd_prime_pow] at v
      obtain ⟨k, hk, hpk⟩ := v  -- then k = 0, 1, 2
      interval_cases k
      .
        simp at hpk
        zify at hpk
        specialize l p rp
        have sp: 3 ≤ (p :ℤ) := by nlinarith
        have ll: 3 ≤ f p := by nlinarith
        rw [show |f p| = f p by apply abs_of_nonneg; nlinarith] at hpk
        simp [hpk] at ll
      .
        simp at hpk
        zify at hpk
        rw [show |f p| = f p by apply abs_of_nonneg; nlinarith] at hpk
        exact hpk
      .
        zify at hpk
        rw [show |f p| = f p by apply abs_of_nonneg; nlinarith] at hpk
        specialize u p
        have sp: 2 ≤ (p :ℤ) := by nlinarith
        simp [sp] at u
        simp [hpk] at u

      exact pp

    specialize h p t
    simp [rp, ht, fp] at h

    -- then we arrive at a contradiction from h
    have c: t + p ∣ t * f t - t ^ 2 := by
      have eq: t * f t - t ^ 2 = (t + p) * (f t + p - t) - (p ^ 2 + p * f t) := by
        ring
      rw [eq]
      clear eq
      apply dvd_sub
      simp
      rw [show t + p = p + t by ring]
      exact h
    by_contra! s
    specialize l t ht
    replace s: 0 < t * f t - t ^ 2 := by
      rw [show  t * f t - t ^ 2 = t * (f t - t) by ring]
      apply lt_of_le_of_ne
      nlinarith
      by_contra! q
      simp at q
      omega
    apply exists_eq_mul_right_of_dvd at c
    obtain ⟨k, hk⟩ := c
    have ok: 0 < k := by nlinarith  -- then there is a size contradiction at c
    nlinarith
    
    
  -- the backward direction: show that f(n) = n is a solution
  .
    intro h
    intro a b hab
    rcases hab with ⟨ha, hb⟩
    have la:= h a ha
    have lb:= h b hb
    simp [la, lb]
    rw [show a ^ 2 + a * b = a * (a + b) by ring]
    simp