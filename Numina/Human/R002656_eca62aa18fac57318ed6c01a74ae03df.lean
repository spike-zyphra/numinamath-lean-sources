import Mathlib

/-- Let m and n be positive integers satisfying the conditions
    ∙ gcd(m+n,210)=1,
    ∙ m^m is a multiple of n^n, and
    ∙ m is not a multiple of n.
    Find the least possible value of m+n. -/
theorem number_theory_98043 :
    IsLeast {k | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ (m + n).Coprime 210 ∧ n ^ n ∣ m ^ m ∧ ¬m % n = 0 ∧ k = m + n} 407 := by
  constructor
  -- m = 286, n = 121 fulfills the conditions, such that 407 is a possible candidate.
  · refine ⟨286,121,?goal⟩
    split_ands
    · norm_num
    · norm_num
    · norm_num
    · trans 11 ^ 286
      -- 11 ^ 286 contains all the "needed powers" of 121
      · change (11 ^ 2) ^ 121 ∣ 11 ^ 286
        rw[← pow_mul]
        apply Nat.pow_dvd_pow _ (by norm_num)
      · apply pow_dvd_pow_of_dvd
        norm_num
    · norm_num
    · rfl
  -- We show this pair is indeed minimal.
  · rintro _ ⟨m,n,mpos,npos,gcd,div,ndiv,rfl⟩
    -- Note that clearly, n > 1 since otherwise m is a multiple.
    have not1 : n ≠ 1 := by
      rintro rfl
      simp[Nat.mod_one] at ndiv
    have gt1 : n > 1 := by
      cases n with
      | zero => exact (npos.false).elim
      | succ n => cases n with
        | zero => simp at not1
        | succ n => simp
    -- Let p be a prime divisor of n,
    have all_primes (p : ℕ) (h : p.Prime) (h' : p ∣ n) : p ∣ m := by
      -- then it is one of n^n,
      have : p ∣ n ^ n := dvd_pow h' npos.ne.symm
      -- of m^m,
      have : p ∣ m ^ m := this.trans div
      -- and due to primality one of m. We will use this property repeatedly.
      apply (h.prime.dvd_pow_iff_dvd mpos.ne.symm).mp this
    -- Also, n is coprime to 210:
    have coprime : n.Coprime 210 := by
      by_contra h
      -- If it was not, they would share a prime divisor p,
      rw[Nat.Prime.not_coprime_iff_dvd] at h
      obtain ⟨p,hp,pn,p210⟩ := h
      -- which would also divide m,
      have pm := all_primes p hp pn
      -- hence m + n, contradiction.
      have : p ∣ m + n := Nat.dvd_add pm pn
      apply Nat.not_coprime_of_dvd_of_dvd
      · exact hp.one_lt
      · exact this
      · exact p210
      · exact gcd
    -- Since 210 has 2,3,5,7 as factors, any prime dividing n must be >= 11.
    have prime_le (p : ℕ) (hp : p.Prime) (h' : p ∣ n) : 11 ≤ p := by
      rw[← not_lt]
      intro h
      have : p ≥ 2 := Nat.succ_le_of_lt hp.one_lt
      have : p.Coprime 210 := coprime.of_dvd_left h'
      interval_cases p <;> norm_num at this
    -- Furthermore, n is not squarefree - if it was,
    have nsqu : ¬ Squarefree n := by
      intro hs
      -- from n | m^m it would also follow that
      have : n ∣ m ^ m := by trans n ^ n; apply dvd_pow (dvd_refl _) npos.ne.symm; exact div
      -- n | m, contradiction.
      rw[hs.dvd_pow_iff_dvd mpos.ne.symm] at this
      rw[← Nat.dvd_iff_mod_eq_zero] at ndiv
      exact ndiv this
    rw[Nat.squarefree_iff_prime_squarefree] at nsqu
    push_neg at nsqu
    -- Hence we can pick a p with p^2|n.
    obtain ⟨p,prp, divp⟩ := nsqu
    -- Now consider the special case n = p^2.
    have p_bound p (hp : p.Prime) (hn : n = p^2) : 2 * p ^ 2 ≤ m := by
      rcases hn
      -- In this case, p | m, but p^2 = n cannot divide m.
      have mp : p ∣ m := all_primes p hp ⟨p, Nat.pow_two p⟩
      have mp2 : ¬ (p^2 ∣ m) := by rwa[← Nat.dvd_iff_mod_eq_zero] at ndiv
      -- But n ^ n = p ^ (2p^2) divides p^m | m ^ m
      convert_to p ^ (2 * p ^ 2) ∣ m ^ m at div
      · rw[← pow_mul]
      · rw[← not_lt]
        intro le
        obtain ⟨q,eq⟩ := Nat.exists_eq_succ_of_ne_zero (n := 2 * p ^ 2)
          (Nat.mul_ne_zero (by simp) (pow_ne_zero 2 hp.ne_zero))
        -- and if 2 * p ^ 2 > m, a p^2 factor would appear in m.
        have : p ^ (2 * p^2) ∣ m ^ (2 * p^2 - 1) := by
          rw[eq,Nat.lt_succ] at le
          rw[eq] at div
          rw[eq, Nat.succ_sub_one]
          apply div.trans
          apply Nat.pow_dvd_pow _ le
        obtain ⟨k, rfl⟩ := mp
        rw[mul_pow, eq, pow_succ, Nat.succ_sub_one] at this
        have powerp := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) this
        have kp : ¬ p ∣ k := by
          intro hk
          apply mp2
          rw[pow_two]
          apply Nat.mul_dvd_mul_left p hk
        apply kp (hp.dvd_of_dvd_pow powerp)
    -- Hence 2p^2 <= m.
    -- For n = 121,
    have n121 (hn : n = 121) : 286 ≤ m := by
      rcases hn
      have m11 : 11 ∣ m := all_primes 11 (by norm_num) (by norm_num)
      -- we immediately get 242 <= m.
      have m242 : 242 ≤ m := p_bound 11 (by norm_num) rfl
      obtain ⟨k, rfl⟩ := m11
      have : 11 * 21 ≤ 11 * k := by trans 242; norm_num; exact m242
      have := Nat.le_of_mul_le_mul_left this (by norm_num)
      rw[← not_lt, Nat.lt_succ]
      intro le
      -- This can be improved to 286 <= m, since all in between multiples of 11 share a divisor with 210.
      have : 11 * k < 11 * 26:= by apply lt_of_le_of_lt; exact le; norm_num
      have := Nat.lt_of_mul_lt_mul_left this
      interval_cases k <;> norm_num at gcd
    -- For n = 169, 338 <= m follows similarly.
    have n169 (hn : n = 169) : 338 ≤ m := by
      rcases hn
      have m13 : 13 ∣ m := all_primes 13 (by norm_num) (by norm_num)
      exact p_bound 13 (by norm_num) rfl
    -- We reduce the situation to the three options n = 121, n = 169, 242 <= n.
    have options : n = 121 ∨ n = 169 ∨ 242 ≤ n := by
      specialize prime_le p prp (dvd_of_mul_left_dvd divp)
      -- If n < 242, p < 16 must hold since 16^2 = 256.
      have p_ub : n < 242 → p < 16 := by
        intro hn
        rw[← not_le]
        intro hp
        have : 256 ≤ p^2 := (sq_le_sq₀ (a := 16) (b := p) (by simp) (by simp)).mpr hp
        rw[← pow_two] at divp
        have := this.trans $ Nat.le_of_dvd npos divp
        linarith
      rw[← or_assoc]
      apply Classical.or_iff_not_imp_right.mpr
      rw[not_le]
      intro h
      specialize p_ub h
      -- But 121 and 169 have no further multiples below 242, so these cases can be excluded as well.
      obtain (rfl|rfl) : p = 11 ∨ p = 13 := by
        interval_cases p
        · exact Or.inl rfl
        · exfalso; norm_num at prp
        · exact Or.inr rfl
        · exfalso; norm_num at prp
        · exfalso; norm_num at prp
      · obtain ⟨k,rfl⟩ := divp
        left
        obtain rfl : k = 1 := by linarith
        rfl
      · obtain ⟨k,rfl⟩ := divp
        right
        obtain rfl : k = 1 := by linarith
        rfl
    -- At last, from n^n <= m^m we get n <= m. Hence for 242 <= n, 484 <= n + m such that this case cannot be minimal.
    -- Since 169 + 338 > 407 = 121 + 286, neither can the case n = 169 be.
    -- Hence n = 121, m = 286 must be the optimum.
    have le : n ≤ m := by
      have pow_le : n ^ n ≤ m ^ m := Nat.le_of_dvd (pow_pos mpos _) div
      rwa[StrictMonoOn.le_iff_le Nat.pow_self_strictMonoOn npos.ne.symm mpos.ne.symm] at pow_le
    rcases options with (rfl|rfl|le2)
    · specialize n121 rfl
      linarith
    · specialize n169 rfl
      linarith
    · linarith