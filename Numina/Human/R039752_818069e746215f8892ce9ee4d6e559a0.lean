import Mathlib
/- N2) Find all triplets $(a, b, p)$ of strictly positive integers where $p$ is prime and the equation


$$

(a+b)^{p}=p^{a}+p^{b}

$$


is satisfied. -/

theorem number_theory_262111 (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : Nat.Prime p) (h : (a + b) ^ p = p ^ a + p ^ b) : (a, b, p) = (1, 1, 2) := by
--For some lemmas, it will be useful to have the "fact" that p is prime.
  have : Fact (Nat.Prime p) := by
        rw [fact_iff]
        exact hp
--The end of the proof will use the following lemma that p-powers of distinct natural numbers differ by more than 1.
  have p_pow_diff (z w : ℕ) (hzw : w < z) (hwpos : 0 < w) : 1 < z ^ p - w ^ p := by
    rw [lt_iff_exists_add] at hzw
    obtain ⟨t, htpos, ht⟩ := hzw
    rw [ht]
    have : w ^ p + t ^ p < (w + t) ^ p := by
      rw [lt_iff_exists_add, add_pow_prime_eq hp]
      use (p * ∑ k ∈ Finset.Ioo 0 p, w ^ k * t ^ (p - k) * (p.choose k / p))
      constructor
      · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos]
        constructor
        · exact Nat.Prime.pos hp
        · apply Finset.sum_pos'
          · intro i hi
            positivity
          · use 1
            simp only [Finset.mem_Ioo, zero_lt_one, true_and, pow_one, Nat.choose_one_right, CanonicallyOrderedCommSemiring.mul_pos, Nat.div_pos_iff, le_refl, and_true]
            constructor
            · exact Nat.Prime.one_lt hp
            · constructor
              · constructor
                · exact hwpos
                · positivity
              · exact Nat.Prime.pos hp
      rfl
    have : t ^ p < (w + t) ^ p - w ^ p := by
      rw [Nat.lt_sub_iff_add_lt, add_comm]
      exact this
    apply lt_of_le_of_lt _ this
    exact Nat.one_le_pow p t htpos
--We first consider the case where a=b.
  by_cases hab : a = b
  · subst hab
    ring_nf at h
--Manipulating the equation, we observe that 4 divides 2^p (since p is at least 2), and therefore it divides a^p * 2^p = p ^ a * 2. It follows that p=2.
    have four_dvd : 4 ∣ a ^ p * 2 ^ p := by
      have : 2 ≤ p := Nat.Prime.two_le hp
      use a ^ p * 2 ^ (p - 2)
      rw [(by omega : 4 = 2 ^ 2), mul_comm (2 ^ 2), mul_assoc, ← pow_add, (by omega : p - 2 + 2 = p)]
    rw [h] at four_dvd
    have p_two : 2 ∣ p ^ a := by
      by_contra h2
      rw [(by omega : 4 = 2 ^ 2)] at four_dvd
      have := Prime.pow_dvd_of_dvd_mul_left (by rw [← Nat.prime_iff]; exact Nat.prime_two) 2 h2 four_dvd
      contradiction
    apply Nat.Prime.dvd_of_dvd_pow Nat.prime_two at p_two
    rw [Nat.dvd_prime hp] at p_two
    simp only [OfNat.ofNat_ne_one, false_or] at p_two
    subst p_two
    rw [pow_two 2, ← mul_assoc] at h
    simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at h
--We consider separately the cases where a=1 (which yields the solution (1,1,2)) and a>1 (which gives a contradiction).
    by_cases h1 : a = 1
    · subst a
      ring_nf at h
      rfl
--First of all, we observe that 2 ^ (a - 1) is even (because a is at least 2).
    · have : Even (2 ^ (a - 1)) := by
          rw [even_iff_two_dvd]
          use 2 ^ (a - 2)
          nth_rw 2 [← pow_one 2]
          rw [← pow_add, (by omega : 1 + (a - 2) = a - 1)]
      nth_rw 2 [(by omega : a = (a - 1) + 1)] at h
      rw [pow_add, pow_one] at h
      simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at h
--It follows that a must be even, since a ^ 2 = 2 ^ (a - 1).
      have even_a : Even a := by
        rw [← h, Nat.even_pow] at this
        exact this.1
--But a must also be odd, since the equality a ^ 2 = 2 ^ (a - 1) gives that 2 ^ (a - 1) is a square, thus a - 1 is even.
      have odd_a : Odd a := by
        have : IsSquare (2 ^ (a - 1)) := by
          rw [← h]
          exact IsSquare.sq a
        obtain ⟨r, hr⟩ := this
        have : r ∣ 2 ^ (a - 1) := by use r
        rw [Nat.dvd_prime_pow Nat.prime_two] at this
        obtain ⟨k,hk⟩ := this
        rw [hk.2, ← pow_add] at hr
        simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
          pow_right_inj₀] at hr
        rw [Nat.odd_iff]
        omega
--Since a cannot be even and odd at the same time, we have found a contradiction.
      rw [← Nat.not_even_iff_odd] at odd_a
      contradiction
--We now consider the case where a ≠ b. First, we observe from the equation that p divides (a + b) ^ p, thus p divides also a + b.
  · have p_dvd_aplusb : p ∣ (a + b) ^ p := by
      use p ^ (a - 1) + p ^ (b - 1)
      ring_nf
      nth_rw 2 4 [← pow_one p]
      rw [← pow_add, (by omega : 1 + (a - 1) = a), ← pow_add, (by omega : 1 + (b - 1) = b)]
      exact h
    apply Nat.Prime.dvd_of_dvd_pow hp at p_dvd_aplusb
    have ⟨k, hk⟩ := p_dvd_aplusb
--Manipulating the equation we have (pk)^p=p^a + p^b, for some k.
    have h' : (p * k) ^ p = p ^ a + p ^ b := by rw [hk] at h; exact h
--It follows that the left-hand side and the right-hand side of the equation have the same p-adic valuation.
    have eq_padic_val : padicValNat p ((p * k) ^ p) = padicValNat p (p ^ a + p ^ b) := by
        rw [h']
--We now consider separately the two cases a < b and a > b.
    by_cases h2 : a < b
--If a < b, we can factor p ^ a from the right-hand side of the equation.
    · have h'' : p ^ a + p ^ b = p ^ a * (1 + p ^ (b - a)) := by
        ring_nf
        rw [← pow_add, (by omega : a + (b - a) = b)]
--We observe that the second factor is coprime to p.
      have not_p_dvd : ¬ p ∣ 1 + p ^ (b - a) := by
        intro hpdvd
        rw [Nat.dvd_add_left (by use p ^ (b - a - 1); nth_rw 2 [← pow_one p]; rw [← pow_add, (by omega : 1 + (b - a - 1) = b - a)])] at hpdvd
        exact Nat.Prime.not_dvd_one hp hpdvd
--We use the equality between p-adic valuations to obtain that p divides a.
      rw [padicValNat.pow p (by rw [← hk]; omega), h'', padicValNat.mul (by simp [Nat.Prime.ne_zero hp] : p ^ a ≠ 0) (by omega), padicValNat.pow a (Nat.Prime.ne_zero hp), padicValNat.self (Nat.Prime.one_lt hp), mul_one, padicValNat.eq_zero_of_not_dvd not_p_dvd, add_zero] at eq_padic_val
      have pdvda : p ∣ a := by use padicValNat p (p * k); rw [eq_padic_val]
--Since p divides a and a + b, it also divides b.      
      have pdvdb : p ∣ b := by
        rw [Nat.dvd_add_right pdvda] at p_dvd_aplusb
        exact p_dvd_aplusb
      obtain ⟨a',ha'⟩ := pdvda
      obtain ⟨b',hb'⟩ := pdvdb
      nth_rw 2 [ha'] at h''
--We rewrite the equation to obtain an equality between a p-power and a p-power times 1 + p ^ (b - a). We deduce that 1 + p ^ (b - a) is also a p-power.
      rw [mul_comm p a', pow_mul] at h''
      have : ∃ z : ℕ, 1 + p ^ (b - a) = z ^ p := by
        have : p ^ a' ∣ a + b := by
          rw [← Nat.pow_dvd_pow_iff (Nat.Prime.ne_zero hp)]
          use 1 + p ^ (b - a)
          rw [← h'']
          exact h
        rw [h''] at h
        obtain ⟨z,hz⟩ := this
        use z
        zify
        rw [← sub_eq_zero]
        rw [hz, mul_pow] at h
        zify at h
        symm at h
        rw [← sub_eq_zero, ← mul_sub,] at h
        simp only [mul_eq_zero, ne_eq, Nat.Prime.ne_zero hp, not_false_eq_true, pow_eq_zero_iff, pow_eq_zero_iff', Nat.cast_eq_zero, false_and, false_or] at h
        exact h
      obtain ⟨z,hz⟩ := this
--The equation gives us that z ^ p - p ^ (b - a) = 1. Since a and b are divisible by p, this is a difference between two distinct p-powers. By the lemma we have seen, this difference is greater than 1. We have a contradiction.      
      have pow_diff : z ^ p - p ^ (b - a) = 1 := by omega
      rw [ha', hb', ← mul_tsub, mul_comm, pow_mul] at pow_diff
      set w := p ^ (b' - a') with hw
      have hwz : w < z := by
        rw [← Nat.pow_lt_pow_iff_left (Nat.Prime.ne_zero hp)]
        omega
      have : 0 < w := by
        rw [hw]
        apply Nat.pos_pow_of_pos
        exact Nat.Prime.pos hp
      have := p_pow_diff z w hwz this
      omega
--We repeat the same argument, with the roles of a and b reversed.      
    · have h2 : b < a := by omega
      have h'' : p ^ a + p ^ b = p ^ b * (1 + p ^ (a - b)) := by
        ring_nf
        rw [← pow_add, (by omega : b + (a - b) = a), add_comm]
      have not_p_dvd : ¬ p ∣ 1 + p ^ (a - b) := by
        intro hpdvd
        rw [Nat.dvd_add_left (by use p ^ (a - b - 1); nth_rw 2 [← pow_one p]; rw [← pow_add, (by omega : 1 + (a - b - 1) = a - b)])] at hpdvd
        exact Nat.Prime.not_dvd_one hp hpdvd
      rw [padicValNat.pow p (by rw [← hk]; omega), h'', padicValNat.mul (by simp [Nat.Prime.ne_zero hp] : p ^ b ≠ 0) (by omega), padicValNat.pow b (Nat.Prime.ne_zero hp), padicValNat.self (Nat.Prime.one_lt hp), mul_one, padicValNat.eq_zero_of_not_dvd not_p_dvd, add_zero] at eq_padic_val
      have pdvdb : p ∣ b := by use padicValNat p (p * k); rw [eq_padic_val]
      have pdvda : p ∣ a := by
        rw [Nat.dvd_add_left pdvdb] at p_dvd_aplusb
        exact p_dvd_aplusb
      obtain ⟨a',ha'⟩ := pdvda
      obtain ⟨b',hb'⟩ := pdvdb
      nth_rw 2 [hb'] at h''
      rw [mul_comm p b', pow_mul] at h''
      have : ∃ z : ℕ, 1 + p ^ (a - b) = z ^ p := by
        have : p ^ b' ∣ a + b := by
          rw [← Nat.pow_dvd_pow_iff (Nat.Prime.ne_zero hp)]
          use 1 + p ^ (a - b)
          rw [← h'']
          exact h
        rw [h''] at h
        obtain ⟨z,hz⟩ := this
        use z
        zify
        rw [← sub_eq_zero]
        rw [hz, mul_pow] at h
        zify at h
        symm at h
        rw [← sub_eq_zero, ← mul_sub,] at h
        simp only [mul_eq_zero, ne_eq, Nat.Prime.ne_zero hp, not_false_eq_true, pow_eq_zero_iff, pow_eq_zero_iff', Nat.cast_eq_zero, false_and, false_or] at h
        exact h
      obtain ⟨z,hz⟩ := this
      have pow_diff : z ^ p - p ^ (a - b) = 1 := by omega
      rw [ha', hb', ← mul_tsub, mul_comm, pow_mul] at pow_diff
      set w := p ^ (a' - b') with hw
      have hwz : w < z := by
        rw [← Nat.pow_lt_pow_iff_left (Nat.Prime.ne_zero hp)]
        omega
      have : 0 < w := by
        rw [hw]
        apply Nat.pos_pow_of_pos
        exact Nat.Prime.pos hp
      have := p_pow_diff z w hwz this
      omega