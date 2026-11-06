import Mathlib

open Nat

/-  Let $n \geqslant 3$ be an integer. For each pair of prime numbers $p$ and $q$ such that $p<q \leqslant n$, Morgane has written the sum $p+q$ on the board. She then notes $\mathcal{P}(n)$ as the product of all these sums. For example, $\mathcal{P}(5)=(2+3) \times(2+5) \times(3+5)=280$.

Find all values of $n \geqslant 3$ for which $n$ ! divides $\mathcal{P}(n)$.

Note: If two sums $p+q$ formed from two different pairs are equal to each other, Morgane writes them both. For example, if $n=13$, she writes both sums $3+13$ and $5+11$.-/
theorem number_theory_290698 {n : ℕ} (hn : 3 ≤ n) :
    n.factorial ∣ (∏ p in (Nat.primesBelow (n+1)), ∏ q in (Nat.primesBelow (n+1)), (if p < q then (p + q) else 1)) ↔ n = 7:= by
    -- Let $n$ be a potential solution, and let $r$ be the largest prime number such that $r \leq n$.
    constructor
    intro hn1
    have hr1 : 3 ∈ Nat.primesBelow (n+1) := by
      refine mem_primesBelow.mpr ?_
      constructor
      linarith
      exact prime_three
    have hr2 : (n + 1).primesBelow.Nonempty := by use 3
    let r := (Nat.primesBelow (n+1)).max' hr2
    have hr3 : r ∈ (Nat.primesBelow (n+1)) := by
      simp [r]
      exact Finset.max'_mem (n + 1).primesBelow hr2
    have hr4 : Nat.Prime r := prime_of_mem_primesBelow hr3
    have h1 : 3 ≤ r := by
      simp [r]
      exact Finset.le_max' (n + 1).primesBelow 3 hr1
    -- Since $r$ divides $n!$, it must also divide $\mathcal{P}(n)$. Therefore, there exist two prime numbers $p$ and $q$ with $p < q \leq n$ such that $r$ divides $p + q$. 
    have h2 : ∃ p ∈ (Nat.primesBelow (n+1)), ∃ q ∈ (Nat.primesBelow (n+1)), r ∣ (p+q) ∧ p < q := by
      have : r ∣ n.factorial := by
        have : r ≤ n := by
          simp [r]
          intro a ha
          apply Nat.lt_of_mem_primesBelow at ha
          linarith
        apply Nat.dvd_factorial ;linarith ;exact this
      have this' := dvd_trans this hn1
      have h3 : ∃ p ∈ (Nat.primesBelow (n+1)), r ∣ ∏ q ∈ (n + 1).primesBelow, if p < q then p + q else 1 := by
        apply Prime.exists_mem_finset_dvd ?_ this'
        exact prime_iff.mp hr4
      rcases h3 with ⟨p,hp,h3⟩
      have h4 : ∃ q ∈ (n + 1).primesBelow, r ∣ if p < q then p + q else 1 := by
        apply Prime.exists_mem_finset_dvd
        exact prime_iff.mp hr4
        exact h3
      rcases h4 with ⟨q,hq,h4⟩
      use p ;constructor ;exact hp
      use q ;constructor ;exact hq
      by_cases h : ¬ p < q
      · simp [h] at h4
        linarith
      simp at h
      simp [h] at h4
      simp [h4,h]
    rcases h2 with ⟨p,hp,⟨q,hq,h5,h6⟩⟩
    -- By the maximality of $r$, we know that $p + q < 2r$, which implies $p + q = r$. Since $q$ and $r$ are odd, $p$ must be even, and thus $p = 2$.
    have h7 : p + q < 2 * r := by
      rw [two_mul]
      have : q ≤ r := Finset.le_max' (n + 1).primesBelow q hq
      linarith
    replace h5 : r = p + q := by
      apply exists_eq_mul_left_of_dvd at h5
      rcases h5 with ⟨c,h5⟩
      by_cases hc : 2 ≤ c
      · nlinarith
      push_neg at hc
      interval_cases c
      rw [zero_mul] at h5 ;linarith
      rw [h5,one_mul]
    have hp1 : Nat.Prime p := prime_of_mem_primesBelow hp
    have hq1 : Nat.Prime q := prime_of_mem_primesBelow hq
    have hp2 : 2 ≤ p := Prime.two_le hp1
    have hq2 : Odd q := by 
      apply Nat.Prime.odd_of_ne_two hq1
      linarith
    have hr5 : Odd r := by
      apply Nat.Prime.odd_of_ne_two hr4
      linarith
    rw [h5,add_comm] at hr5
    apply Nat.odd_add.mp at hr5
    replace hp2 := hr5.mp hq2
    apply (Nat.Prime.even_iff hp1).mp at hp2
    -- Similarly, there exist two prime numbers $s$ and $t$ with $s < t \leq n$ such that $q$ divides $s + t$. We will now prove that $q - 2$ is also prime.
    -- If $t \leq q$, then $s + t = q$, which implies $s = 2$ and $t = q - 2$.
    -- Otherwise, $t = r = q + 2$, and since $q < s + t < 2q + 2 < 3q$, it follows that $s + t = 2q$, and thus $s = q - 2$.
    have h3 : ∃ s ∈ (Nat.primesBelow (n+1)), ∃ t ∈ (Nat.primesBelow (n+1)), q ∣ (s+t) ∧ s < t := by
      have : q ∣ n.factorial := by
        have : q ≤ n := by
          apply lt_of_mem_primesBelow at hq ;linarith
        apply Nat.dvd_factorial ;linarith ;exact this
      have this' := dvd_trans this hn1
      have h3 : ∃ s ∈ (Nat.primesBelow (n+1)), q ∣ ∏ t ∈ (n + 1).primesBelow, if s < t then s + t else 1 := by
        apply Prime.exists_mem_finset_dvd ?_ this'
        exact prime_iff.mp (prime_of_mem_primesBelow hq)
      rcases h3 with ⟨s,hs,h3⟩
      have h4 : ∃ t ∈ (n + 1).primesBelow, q ∣ if s < t then s + t else 1 := by
        apply Prime.exists_mem_finset_dvd
        apply prime_iff.mp
        exact prime_of_mem_primesBelow hq
        exact h3
      rcases h4 with ⟨t,ht,h4⟩
      use s ;constructor ;exact hs
      use t ;constructor ;exact ht
      by_cases h : ¬ s < t
      · simp [h] at h4
        linarith
      simp at h
      simp [h] at h4
      simp [h4,h]
    rcases h3 with ⟨s,hs,⟨t,ht,h8,h9⟩⟩
    have h10 : (q-2) ∈ (n + 1).primesBelow := by
      by_cases h : t ≤ q
      · have h11 : s + t < 2 * q := by
          rw [two_mul]
          linarith
        replace h8 : q = s + t := by
          apply exists_eq_mul_left_of_dvd at h8
          rcases h8 with ⟨c,h8⟩
          by_cases hc : 2 ≤ c
          · nlinarith
          push_neg at hc
          interval_cases c
          rw [zero_mul] at h8 ;linarith
          rw [h8,one_mul]
        have hs1 : Nat.Prime s := prime_of_mem_primesBelow hs
        have ht1 : Nat.Prime t := prime_of_mem_primesBelow ht
        have hs2 : 2 ≤ s := Prime.two_le hs1
        have ht2 : Odd t := by 
          apply Nat.Prime.odd_of_ne_two ht1
          linarith
        rw [h8,add_comm] at hq2
        apply Nat.odd_add.mp at hq2
        replace hq2 := hq2.mp ht2
        apply (Nat.Prime.even_iff hs1).mp at hq2
        have : t = q - 2 := by
          rw [h8,hq2,add_comm]
          exact rfl
        rw [← this] ;exact ht
      push_neg at h
      have h11 : t ≤ r := Finset.le_max' (n + 1).primesBelow t ht
      rw [h5,hp2,add_comm] at h11
      apply Nat.eq_or_lt_of_le at h11
      rcases h11 with h11 |h11
      · have h12 : s + (q + 2) < 3 * q := by
          rw [show 3=2+1 by norm_num, add_mul,two_mul,one_mul]
          have : s ≤ q := by
            by_contra!
            have this' : s ≤ r := Finset.le_max' (n + 1).primesBelow s hs
            apply Nat.eq_or_lt_of_le at this'
            rcases this' with h |h
            · linarith
            · have : s = q + 1 := by linarith
              have this' : Even s := by
                rw [this]
                exact Odd.add_one hq2
              apply (Nat.Prime.even_iff (prime_of_mem_primesBelow hs)).mp at this'
              have : q = 1 := by omega
              rw [this] at hq1
              norm_num at hq1
          nlinarith
        replace h8 : 2 * q = s + (q + 2) := by
          apply exists_eq_mul_left_of_dvd at h8
          rcases h8 with ⟨c,h8⟩
          by_cases hc : 3 ≤ c
          · nlinarith
          push_neg at hc
          interval_cases c
          rw [zero_mul] at h8 ;linarith
          linarith
          rw [← h8] ;linarith
        have : s = q - 2 := by
          rify at h8
          have hq3 : 2 ≤ q := Prime.two_le hq1
          rify [hq3] ;linarith
        rw [this] at hs ;exact hs
      replace h : t = q + 1 := by linarith
      have : Even t := by
        rw [h]
        exact Odd.add_one hq2
      apply (Nat.Prime.even_iff (prime_of_mem_primesBelow ht)).mp at this
      have : q = 1 := by omega
      simp [this,Nat.not_prime_one] at hq1
    -- In particular, 3 must divide one of the three prime numbers $q - 2$, $q$, or $q + 2$. Since $q$ and $q + 2$ are primes greater than 3, the only possibility is $q - 2 = 3$, which gives $q = 5$ and $r = q + 2 = 7$.
    have h13 : q = 5 := by
      have hq3 : 2 ≤ q := Prime.two_le hq1
      have : 3 ∣ (q-2) ∨ 3 ∣ q ∨ 3 ∣ (q+2) := by
        let a := q / 3
        let b := q % 3
        have : q = 3*a+b := by
          simp only [a,b]
          exact Eq.symm (div_add_mod q 3)
        have hb : b < 3 := by 
          simp only [b] ;refine mod_lt q (by simp)
        interval_cases b
        · right ;left ;simp [this]
        · right ;right ;rw [show q+2=3*(a+1) by rw [this] ;ring_nf] ;simp
        · left ;rify [hq3] ;simp [this]
      rcases this with h1 | h1 | h1
      · apply (Nat.Prime.dvd_iff_eq (prime_of_mem_primesBelow h10) (by simp)).mp at h1
        omega
      · apply (Nat.Prime.dvd_iff_eq hq1 (by simp)).mp at h1
        apply prime_of_mem_primesBelow at h10
        rw [h1] at h10 ;norm_num at h10
      · rw [h5,hp2,add_comm] at hr4
        apply (Nat.Prime.dvd_iff_eq hr4 (by simp)).mp at h1 ;linarith
    -- Therefore, $n \geq 7$, and $n!$ must divide
    have h14 : 7 ≤ n := by
      have : r < n + 1 := by
        simp [r]
        intro y hy
        exact lt_of_mem_primesBelow hy
      rw [h5,h13,hp2] at this
      norm_num at this ;linarith
    -- $$ \mathcal{P}(n)=(2+3) \times(2+5) \times(2+7) \times(3+5) \times(3+7) \times(5+7)=2^{6} \times 3^{3} \times 5^{2} \times 7 $$
    have h15 : r ≤ 7 := by rw [h5,h13,hp2]
    simp [r] at h15
    replace h15 : (n + 1).primesBelow = {2,3,5,7} := by
      ext x
      constructor
      · intro hx
        have h16 := prime_of_mem_primesBelow hx
        apply h15 at hx
        interval_cases x
        <;> norm_num at h16
        <;> simp
      intro hx
      simp at hx
      rcases hx with hx |hx |hx |hx
      <;> rw [hx]
      <;> apply mem_primesBelow.mpr
      <;> constructor
      <;> norm_num
      <;> linarith
    simp [h15] at hn1
    -- However, $2 \times 4 \times 6 \times 8 = 2^{7} \times 3$ does not divide $\mathcal{P}(n)$, so we must have $n = 7$.
    apply Nat.eq_or_lt_of_le at h14
    rcases h14 with h14 |h14
    · rw [h14]
    replace h14 : 8 ≤ n := by linarith
    apply factorial_dvd_factorial at h14
    have := dvd_trans h14 hn1
    have this' : 8! = 40320 := rfl
    rw [this'] at this
    norm_num at this
    -- Conversely, $n = 7$ is indeed a valid solution, since $7! = 2^{4} \times 3^{2} \times 5 \times 7$ divides $\mathcal{P}(7)$.
    intro hn2
    have : primesBelow 8 = {2,3,5,7} := by
      ext x
      constructor
      · intro hx
        have := prime_of_mem_primesBelow hx
        have this' : x < 8 := lt_of_mem_primesBelow hx
        interval_cases x
        <;> norm_num at this
        <;> simp
      intro hx
      simp at hx
      rcases hx with hx |hx |hx |hx
      <;> rw [hx]
      <;> apply mem_primesBelow.mpr
      <;> constructor
      <;> norm_num
    have this' : 7! = 5040 := rfl
    simp [hn2,this]
    rw [this']; norm_num
      
      
    





      
    
      