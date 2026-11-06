import Mathlib

/- For primes $a, b,c$ that satisfies the following, calculate $abc$. 
$b + 8$ is a multiple of $a$, and $b^2 - 1$ is a multiple of $a$ and $c$. Also, $b + c = a^2 - 1$. -/
theorem number_theory_33335 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : a ∣ b + 8) (h2 : a ∣ b ^ 2 - 1) (h3 : c ∣ b ^ 2 - 1) (h4 : b + c = a ^ 2 - 1) :
    a * b * c = 2009 := by 

    --First, some simple observations from given conditions.
    have : 2 ≤ a := by exact Nat.Prime.two_le ha
    have : 2 ≤ b := by exact Nat.Prime.two_le hb
    have : 2 ≤ c := by exact Nat.Prime.two_le hc
    have : b^2 -1 = (b+1)*(b-1) := by 
      have : ∃ k, k+1=b := by use (b-1); omega
      obtain ⟨k,hk⟩ := this
      rw [← hk]
      ring_nf
      field_simp
      ring_nf
      omega
    rw [this] at h2 h3
    have h4': (b:ℤ) + 1 = a^2 - c := by 
      zify at h4
      have : @Nat.cast ℤ instNatCastInt (a ^ 2 - 1) = (a:ℤ)^2 - 1 := by
        have : 1 < a^2 := by nlinarith
        have : 0 < a^2 -1 := by linarith
        field_simp
      rw [this] at h4
      omega

    --Since a ∣ b^2-1, we have a ∣ b+1 ∨ a ∣ b-1.
    have h2' : a ∣ (b+1) ∨ a ∣ (b-1) := by exact (Nat.Prime.dvd_mul ha).mp h2
    rcases h2' with h2 | h2
    --The case a ∣ (b+1)
    --Since we also have a ∣ b+8, we get a = 7;
    --Then, use the equation above, we can have a ∣ c and hence c = 7.
    --Finally we get b = 41 and hence abc = 2009.
    have t1: a ∣ (b+8)-(b+1) := by exact Nat.dvd_sub' h1 h2
    have : (b+8)-(b+1) = 7 := by omega
    rw [this] at t1 
    have: Nat.Prime 7 := by norm_num
    have ae7: a = 7 := by exact (Nat.prime_dvd_prime_iff_eq ha this).mp t1
    zify at h2
    rw [h4'] at h2
    have : (a:ℤ) ∣ (c:ℤ) := by 
      have t1: (a:ℤ) ∣ a^2 := by use a; ring
      have : (a:ℤ) ∣ (a:ℤ)^2 - (c:ℤ) - a^2 := by exact Int.dvd_sub h2 t1
      simp at this
      exact this
    norm_cast at this
    have : a = c := by exact (Nat.prime_dvd_prime_iff_eq ha hc).mp this
    have ce7 : c = 7 := by linarith
    rw [ae7,ce7] at h4'
    norm_num at h4'
    have be41 : b = 41 := by nlinarith
    rw [ae7,be41,ce7] 
    
    --The case a ∣ b - 1
    --Since a ∣ b+8 too, we have a = 3 and hence b+c=8, but then no matter the value of b is, there is a contradiction.
    have ae3: a = 3 := by
      have t2: a ∣ (b+8) - (b-1) := by exact Nat.dvd_sub' h1 h2
      have : (b+8)-(b-1)=9 := by omega
      rw [this] at t2
      have : 9 = 3 * 3 := by norm_num
      rw [this] at t2
      have : Nat.Prime 3 := by norm_num
      have ad3: a ∣ 3 ∨ a ∣ 3 := by exact (Nat.Prime.dvd_mul ha).mp t2
      simp at ad3
      exact (Nat.prime_dvd_prime_iff_eq ha this).mp ad3
    rw [ae3] at h4
    norm_num at h4
    
    by_cases be2 : b=2
    have ce: c = 6 := by omega
    rw [ce] at hc;
    norm_num at hc

    by_cases be3 : b=3
    have ce: c = 5 := by omega
    rw [ce,be3] at h3
    norm_num at h3

    by_cases be4 : b=4
    rw [be4] at hb
    norm_num at hb

    by_cases be5 : b=5
    rw [ae3,be5] at h1
    norm_num at h1

    have be6: b = 6 := by omega
    rw [be6] at hb
    norm_num at hb
    
    
      

