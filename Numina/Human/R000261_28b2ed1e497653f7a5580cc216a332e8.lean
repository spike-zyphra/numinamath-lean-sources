import Mathlib



import Mathlib
import Aesop
set_option maxHeartbeats 500000
open BigOperators Real Nat Topology Rat
/-Find all prime numbers  $ p $  for which  $ 1 + p\cdot 2^{p} $  is a perfect square.-/

theorem number_theory_8736(p:ℕ)(h1:Nat.Prime p)(h2:∃ n : ℕ, (1 + p * 2^p = n^2)): p=2 ∨ p=3 := by
    -- case1 p<5
    by_cases hp: p<6
    interval_cases p
    -- consider p=0-4
    any_goals trivial
    -- consider p=5
    rcases h2 with ⟨n,h2⟩
    simp at h2
    -- prove 161 != n^2
    -- prove n<13
    by_cases hn: n<13
    interval_cases n
    repeat linarith
    -- consider n>=13
    have hn: 13 ≤ n := by omega
    -- prove 169<=n^2
    have hn2: 13*13≤n^2 := by rw [pow_two];apply Nat.mul_le_mul;exact hn;exact hn
    -- prove contradition
    rw [← h2] at hn2
    trivial

    -- case2 p>=6
    apply False.elim
    --    Suppose \( p \geq 5 \) and \( 1 + p \cdot 2^p = x^2 \). Then: (x-1)(x+1) = p \cdot 2^p
    rcases h2 with ⟨n, hn⟩
    -- prove n>0
    have h4: n>0 := by
        by_contra h0
        simp at h0
        rw [h0] at hn
        simp at hn
    -- prove n^2>1
    have h5: 1<= n^2 := by omega
    -- prove n^2-1=p*2^p
    have h3: n^2 - 1 + 1 = p * 2^p + 1 := by rw [Nat.sub_add_cancel h5]; linarith
    simp at h3
    -- prove (n+1)*(n-1)=p*2^p
    have h6: (n+1)*(n-1) = n^2-1 := by cases n;simp;simp;linarith
    have h7: (n+1)*(n-1) = p * 2^p := by rw [h3] at h6;exact h6
    -- prove p*2^p is even
    have h9: Even (p * 2^p) := by
        rw [Nat.even_mul]
        right
        rw [Nat.even_pow]
        constructor
        decide
        linarith
    -- prove n is odd
    have h8: Odd n := by
        by_contra hodd
        -- prove n^2 is even
        simp at hodd
        have h10: Even (n*n) := by
            rw [Nat.even_mul]
            left
            exact hodd
        -- prove n^2 is odd
        have h11: Odd (n^2):= by
            rw [← hn]
            apply Even.one_add
            exact h9
        rw [pow_two] at h11
        -- show contradiction
        rw [← Nat.not_even_iff_odd] at h11
        trivial
    -- prove n+1 and n-1 are even
    have h12: Even (n+1) := by
        apply Odd.add_odd
        -- use n is odd
        exact h8
        decide
    have h13: Even (n-1) := by
        by_contra hodd
        -- use n is odd
        simp at hodd
        have h14: Even (n-1+1) := by
            apply Odd.add_odd
            exact hodd
            decide
        -- prove n-1+1=n
        rw [Nat.sub_add_cancel h4] at h14
        -- show contradiction
        rw [← Nat.not_even_iff_odd] at h8
        trivial
    -- prove  \( y = \frac{x-1}{2} \) and \( z = \frac{x+1}{2} \). Then:
    rcases h12 with ⟨y, hy⟩
    rcases h13 with ⟨z, hz⟩
    have h2y: y+y=2*y := by ring
    have h2z: z+z=2*z := by ring
    -- rewrite n with y
    rw [hy,h2y] at h7
    rw [hz,h2z] at h7
    -- prove y*z=p*2^(p-2)
    have hp2: p = p - 2 + 2 := by rw [Nat.sub_add_cancel]; linarith
    nth_rw 2 [hp2] at h7
    -- 2^p=2^(p-2)*4
    rw [pow_add] at h7
    ring_nf at h7
    -- prove y*z=p*2^(p-2)
    simp at h7
    -- prove y=z+1
    -- prove n = z+z+1
    have h15: n = z+z+1 := by rw [← hz]; rw [Nat.sub_add_cancel]; linarith
    rw [h15] at hy
    have h16: y = z+1 := by linarith
    -- prove z*(z+1)=p*2^(p-2)
    rw [h16] at h7
    -- show z+1 and z are coprime
    have hcoprime: Nat.Coprime z (z+1) := by
        rw [ Nat.coprime_iff_gcd_eq_one]
        simp
    -- show p < 2^(p-2)
    -- first show 2(p-3)<2^(p-2)
    have h17: (p-3)<2^(p-3) := by apply Nat.lt_pow_self (by norm_num)
    have h18: 2*(p-3)<2^(p-3)*(2^1) := by linarith
    rw [← pow_add] at h18
    have h19: (p - 3)  = p - (2 + 1) := by linarith
    -- prove p-3+1=p-2
    nth_rw 2 [h19] at h18
    rw [Nat.sub_add_eq] at h18
    rw [Nat.sub_add_cancel] at h18
    -- prove p < 2*(p-3)
    have h20: p ≤ 2*(p-3) := by omega
    have h21: p < 2^(p-2) := by linarith
    -- show p ∣ z+1 or p ∣ z
    have h22: p∣ z+1 ∨ p ∣ z := by
        rw [← Nat.Prime.dvd_mul]
        rw [h7]
        simp
        exact h1
    -- cases 1 p ∣ z+1
    cases h22
    rename_i hleft
    -- show p ¬ | z
    rcases hleft with ⟨k, hk⟩
    rw [hk] at h7
    -- eliminate p
    rw [mul_assoc] at h7
    simp at h7
    have hpnz: p ≠ 0 := by omega
    -- show kz=2^(p-2)
    cases h7
    rename_i hright
    -- cases 1: k=1
    by_cases hk1:k=1
    rw [hk1] at hright
    rw [hk1] at hk
    -- contradiction
    simp at hk
    linarith
    -- cases 2: k=0
    by_cases hk0:k=0
    rw [hk0] at hk
    simp at hk
    -- cases 3: k>=2
    have hk2: k ≥ 2 := by omega
    -- prove z.Corpime k
    have hcoprime1: Nat.Coprime k z := by
        rw [hk] at hcoprime
        rw [Nat.coprime_comm] at hcoprime
        apply Nat.Coprime.coprime_mul_left
        exact hcoprime


    -- consider prime factors of k
    have hpf: k.primeFactors ⊆ {2} := by
        -- consider (k*z).primeFactors = {2}
        have h99: (k*z).primeFactors = {2} := by rw [hright];apply Nat.primeFactors_prime_pow;linarith;decide
        -- show k.primeFactors ⊆ {2}
        rw [Nat.Coprime.primeFactors_mul] at h99
        -- use coprime
        rw [← h99]
        apply Finset.subset_union_left
        exact hcoprime1
    -- show the rest part of equal
    simp at hpf
    -- consider 3 cases for k
    cases hpf
    omega
    -- show 2 ∣ k
    rename_i h23
    have h23: 2 ∣ k := by
        apply Nat.dvd_of_mem_primeFactors
        rw [h23]
        simp
    -- now show contradiction by z∣k


    -- consider prime factors of k
    have hpf: z.primeFactors ⊆ {2} := by
        -- consider (k*z).primeFactors = {2}
        have hpf1: (k*z).primeFactors = {2} := by
            rw [hright]
            apply Nat.primeFactors_prime_pow
            linarith
            decide
        -- show k.primeFactors ⊆ {2}
        rw [Nat.Coprime.primeFactors_mul] at hpf1
        -- use coprime
        rw [← hpf1]
        apply Finset.subset_union_right
        exact hcoprime1
    -- show the rest part of equal
    simp at hpf
    -- consider 3 cases for k
    cases hpf

    -- proof z!=0 and z!=1
    rename_i hzz
    -- case1 z=0
    cases hzz
    rename_i hzz0
    rw [hzz0] at hright
    simp at hright
    -- prove 2^(p-2)!=0
    linarith
    -- case2 z=1
    rename_i hzz1
    rw [hzz1] at hk
    simp at hk
    -- prove 2!=pk
    have hp:6≤p := by omega
    -- prove p*k>10
    have hpk: 6*2 ≤ p*k := by apply Nat.mul_le_mul;exact hp;linarith
    -- prove contradiction
    linarith
    -- show 2 ∣ z
    rename_i h24
    have h25: 2 ∣ z := by
        apply Nat.dvd_of_mem_primeFactors
        rw [h24]
        simp
    -- show contradiction by 2 | gcd z (z+1)
    rw [Nat.coprime_iff_gcd_eq_one] at hcoprime1
    have h26:= Nat.dvd_gcd h23 h25
    -- show 2 | 1
    rw [hcoprime1] at h26
    simp at h26
    linarith


    -- cases 2 : p ∣ z
    rename_i hright
    rcases hright with ⟨k, hk⟩
    nth_rw 2 [hk] at h7
    -- eliminate p
    rw [mul_comm,mul_assoc,] at h7
    simp at h7
    have hpnz: p ≠ 0 := by omega
    -- show kz=2^(p-2)
    cases h7
    rename_i hright
    -- cases 1: k=1
    by_cases hk1:k=1
    rw [hk1] at hright
    rw [hk1] at hk
    -- contradiction
    simp at hk
    simp at hright
    -- prove p+1 != 2^(p-2)
    rw [hk] at hright

    -- show p+1 < 2^(p-2)
    -- first show 4(p-4)<2^(p-2)
    have h17: (p-4)<2^(p-4) := by apply Nat.lt_pow_self (by norm_num)
    have h18: 4*(p-4)<2^(p-4)*(2^2) := by linarith
    rw [← pow_add] at h18
    have h19: (p - 4)  = p - (2 + 2) := by linarith
    -- prove p-3+1=p-2
    nth_rw 2 [h19] at h18
    rw [Nat.sub_add_eq] at h18
    rw [Nat.sub_add_cancel] at h18
    -- prove p+1 < 4*p-4
    have h20: p+1 ≤ 4*(p-4) := by omega
    have h21: p+1 < 2^(p-2) := by linarith
    rw [← hright] at h21
    -- find contradiction p+1<p+1
    linarith
    linarith

    -- cases 2: k=0
    by_cases hk0:k=0
    rw [hk0] at hk
    simp at hk
    rw [hk] at hright
    simp at hright
    -- prove 2^(p-2)!=0
    rw [hk0] at hright
    linarith
    -- cases 3: k>=2
    have hk2: k ≥ 2 := by omega
    -- prove z+1.Corpime k
    have hcoprime1: Nat.Coprime k (z+1) := by
        nth_rw 1 [hk] at hcoprime
        apply Nat.Coprime.coprime_mul_left
        exact hcoprime


    -- consider prime factors of k
    have hpf: k.primeFactors ⊆ {2} := by
        -- consider (k*z).primeFactors = {2}
        have hpf1: (k*(z+1)).primeFactors = {2} := by
            rw [hright]
            apply Nat.primeFactors_prime_pow
            linarith
            decide
        -- show k.primeFactors ⊆ {2}
        rw [Nat.Coprime.primeFactors_mul] at hpf1
        -- use coprime
        have h22:= Nat.Coprime.disjoint_primeFactors hcoprime1
        rw [← hpf1]
        apply Finset.subset_union_left
        exact hcoprime1
    -- show the rest part of equal
    simp at hpf
    -- consider 3 cases for k
    cases hpf
    omega
    -- show 2 ∣ k
    rename_i h23
    have h23: 2 ∣ k := by
        apply Nat.dvd_of_mem_primeFactors
        rw [h23]
        simp
    -- now show contradiction by z∣k


    -- consider prime factors of z+1
    have hpf: (z+1).primeFactors ⊆ {2} := by
        -- consider (k*z).primeFactors = {2}
        have hpf1: (k*(z+1)).primeFactors = {2} := by
            rw [hright]
            apply Nat.primeFactors_prime_pow
            linarith
            decide
        -- show k.primeFactors ⊆ {2}
        rw [Nat.Coprime.primeFactors_mul] at hpf1
        -- use coprime
        have h22:= Nat.Coprime.disjoint_primeFactors hcoprime1
        rw [← hpf1]
        apply Finset.subset_union_right
        exact hcoprime1
    -- show the rest part of equal
    simp at hpf
    -- consider 3 cases for k
    cases hpf
    rename_i hz0
    -- use p*k
    rw [hz0] at hk
    simp at hk
    -- use omega
    omega


    -- show 2 ∣ z
    rename_i h24
    have h25: 2 ∣ (z+1) := by
        apply Nat.dvd_of_mem_primeFactors
        rw [h24]
        simp
    -- show contradiction by 2 | gcd z (z+1)
    rw [Nat.coprime_iff_gcd_eq_one] at hcoprime1
    have h26:= Nat.dvd_gcd h23 h25
    -- show 2 | 1
    rw [hcoprime1] at h26
    simp at h26
    linarith
    -- prove residue cases
    linarith
