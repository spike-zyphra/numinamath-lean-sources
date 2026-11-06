import Mathlib

-- lemma lem_when_q_prime (p n q : ℕ) (hp : Nat.Prime p) (hq' : Nat.Prime q)
--     (hn : 0 < n) (hq : q > 0 ∧ q ∣ (n + 1)^p - n^p) : p ∣ q - 1 := by sorry

/- Let $p$ be a prime number and let $n$ be a positive integer. Let $q$ be a positive divisor of $(n+1)^{p}-n^{p}$. Show that $q-1$ is divisible by $p$. -/
theorem number_theory_239291 (p n q : ℕ) (hp : Nat.Prime p) (hn : 0 < n)
    (hq : q > 0 ∧ q ∣ (n + 1)^p - n^p) : p ∣ q - 1 := by

    -- It is sufficient to show the statement for $q$ prime.
    wlog hq' : Nat.Prime q
    · suffices h : q ≡ 1 [ZMOD p] by
        refine (Nat.modEq_iff_dvd' ?_).mp ?_
        linarith only [hq.1]
        exact Int.natCast_modEq_iff.mp (id (Int.ModEq.symm h))

      have qnz : q ≠ 0 := by linarith only [hq.1]
      rw [
        ← Nat.factorization_prod_pow_eq_self qnz,
        Finsupp.prod,
        Nat.support_factorization,
        Finset.prod_natCast,
      ]
      simp only [Nat.cast_pow]

      unfold Int.ModEq
      rw [Finset.prod_int_mod]

      have h_q'_modeq_1 : ∀ q' ∈ q.primeFactors, q' ≡ 1 [ZMOD p] := by
        intro q' q'mem
        have h_q'_dvd_q : q' ∣ q := by exact Nat.dvd_of_mem_primeFactors q'mem
        have h_q'_dvd_sub : q' ∣ (n + 1)^p - n^p := by
          trans q
          exact h_q'_dvd_q
          exact hq.2
        have q'pos : q' > 0 := by exact Nat.pos_of_mem_primeFactors q'mem
        have := this p n q'
          hp hn ⟨q'pos, h_q'_dvd_sub⟩ (Nat.prime_of_mem_primeFactors q'mem)
        symm
        apply Int.modEq_iff_dvd.mpr
        have : q' - (1 : ℤ) = ↑(q' - 1) := Eq.symm (Int.natCast_pred_of_pos q'pos)
        rw [this]
        norm_cast

      have h_q'_pow_modeq_1 : ∀ q' ∈ q.primeFactors, ∀ n, q' ^ n ≡ 1 [ZMOD p] := by
        intro q' q'mem n
        rw [show (1 : ℤ) = 1 ^ n by ring]
        exact Int.ModEq.pow n (h_q'_modeq_1 q' q'mem)

      have : ∏ i ∈ q.primeFactors, (i : ℤ) ^ q.factorization i % p =
        ∏ i ∈ q.primeFactors, 1 := by
          apply Finset.prod_congr rfl
          intro q' q'mem
          have : (1 : ℤ) = 1 % p := by
            refine Eq.symm (Int.emod_eq_of_lt ?_ ?_)
            norm_num
            norm_cast
            exact Nat.Prime.one_lt hp
          rw [this]
          change ↑q' ^ q.factorization q' ≡ 1 [ZMOD p]
          exact h_q'_pow_modeq_1 q' q'mem (q.factorization q')
      rw [this]

      simp

    -- We need to prove that
    -- $$ (n+1)^{p} \equiv n^{p} \quad(\bmod q) \Longrightarrow q \equiv 1 \quad(\bmod p) . $$
    have hq2 : (n + 1) ^ p ≡ n ^ p [MOD q] := by
      refine Nat.ModEq.symm ((fun {n a b} h ↦ (Nat.modEq_iff_dvd' h).mpr) ?_ ?_)
      · refine Nat.pow_le_pow_of_le_left ?_ p
        exact Nat.le_add_right n 1
      exact hq.2

    -- It is obvious that $\operatorname{gcd}(n, q)=\operatorname{gcd}(n+1, q)=1$ (as $n$ and $n+1$ cannot be divisible by $q$ simultaneously).
    have h_n_q_gcd_1 : Nat.gcd n q = 1 := by
      let g := gcd n q
      have hg1 : g ∣ n := by exact Nat.gcd_dvd_left n q
      have hg2 : g ∣ n ^ p := dvd_pow hg1 (Nat.Prime.ne_zero hp)
      have hg3 : g ∣ (n + 1) ^ p := by
        suffices h : (g : ℤ) ∣ (n + 1) ^ p by norm_cast at h
        have : (n + 1) ^ p ≡ n ^ p [ZMOD q] := by
          unfold Int.ModEq
          norm_cast
        apply Int.ModEq.symm at this
        apply Int.modEq_iff_add_fac.mp at this
        obtain ⟨t, ht⟩ := this
        rw [ht]
        apply Int.dvd_add
        · norm_cast
        have : (g : ℤ) ∣ q := by
          norm_cast
          exact gcd_dvd_right n q
        exact Dvd.dvd.mul_right this t
      have hg4 : g ∣ gcd (n ^ p) ((n + 1) ^ p) := by apply dvd_gcd; repeat assumption
      have hg5 : g ∣ gcd n ((n + 1) ^ p) ^ p := by
        trans gcd (n ^ p) ((n + 1) ^ p)
        exact hg4
        apply gcd_pow_left_dvd_pow_gcd
      have hg6 : gcd n ((n + 1) ^ p) ∣ gcd n (n + 1) ^ p := by
        apply gcd_pow_right_dvd_pow_gcd
      have hg7 : gcd (n + 1) n = 1 := by
        refine Nat.eq_one_of_dvd_one ?_
        nth_rw 2 [show 1 = n + 1 - n by exact Nat.eq_sub_of_add_eq' rfl]
        apply Nat.dvd_sub
        exact Nat.le_add_right n 1
        exact gcd_dvd_left (n + 1) n
        exact gcd_dvd_right (n + 1) n
      rw [gcd_comm] at hg7
      rw [hg7, one_pow] at hg6
      apply Nat.eq_one_of_dvd_one at hg6
      rw [hg6, one_pow] at hg5
      exact Nat.eq_one_of_dvd_one hg5

    have h_n_succ_q_gcd_1 : Nat.gcd (n + 1) q = 1 := by
      let g := gcd (n + 1) q
      have hg1 : g ∣ (n + 1) := by exact Nat.gcd_dvd_left (n + 1) q
      have hg2 : g ∣ (n + 1) ^ p := dvd_pow hg1 (Nat.Prime.ne_zero hp)
      have hg3 : g ∣ n ^ p := by
        suffices h : (g : ℤ) ∣ n ^ p by norm_cast at h
        have : (n + 1) ^ p ≡ n ^ p [ZMOD q] := by
          unfold Int.ModEq
          norm_cast
        apply Int.modEq_iff_add_fac.mp at this
        obtain ⟨t, ht⟩ := this
        rw [ht]
        apply Int.dvd_add
        · norm_cast
        have : (g : ℤ) ∣ q := by
          norm_cast
          exact gcd_dvd_right (n + 1) q
        exact Dvd.dvd.mul_right this t
      have hg4 : g ∣ gcd (n ^ p) ((n + 1) ^ p) := by apply dvd_gcd; repeat assumption
      have hg5 : g ∣ gcd n ((n + 1) ^ p) ^ p := by
        trans gcd (n ^ p) ((n + 1) ^ p)
        exact hg4
        apply gcd_pow_left_dvd_pow_gcd
      have hg6 : gcd n ((n + 1) ^ p) ∣ gcd n (n + 1) ^ p := by
        apply gcd_pow_right_dvd_pow_gcd
      have hg7 : gcd (n + 1) n = 1 := by
        refine Nat.eq_one_of_dvd_one ?_
        nth_rw 2 [show 1 = n + 1 - n by exact Nat.eq_sub_of_add_eq' rfl]
        apply Nat.dvd_sub
        exact Nat.le_add_right n 1
        exact gcd_dvd_left (n + 1) n
        exact gcd_dvd_right (n + 1) n
      rw [gcd_comm] at hg7
      rw [hg7, one_pow] at hg6
      apply Nat.eq_one_of_dvd_one at hg6
      rw [hg6, one_pow] at hg5
      exact Nat.eq_one_of_dvd_one hg5

    -- Hence there exists a positive integer $m$ such that $m n \equiv 1(\bmod q)$.
    -- In fact, $m$ is just the multiplicative inverse of $n(\bmod q)$.
    have ⟨m, hm⟩ : ∃ m, n * m ≡ 1 [MOD q] := by
      unfold Nat.ModEq
      rw [show 1 % q = 1 by refine Nat.mod_eq_of_lt (Nat.Prime.one_lt hq')]
      refine Nat.exists_mul_emod_eq_one_of_coprime h_n_q_gcd_1 ?_
      exact Nat.Prime.one_lt hq'

    -- Take $s=m(n+1)$.
    let s := m * (n + 1)

    -- It is easy to see that
    -- $$ s^{p} \equiv 1 \quad(\bmod q) $$
    have h_s_pow_p_modeq_1 : s ^ p ≡ 1 [MOD q] := by
      unfold s
      rw [mul_pow]
      trans m ^ p * n ^ p
      · exact Nat.ModEq.mul rfl hq2
      · rw [← mul_pow, show 1 = 1 ^ p by ring]
        refine Nat.ModEq.pow p ?_
        rwa [mul_comm]

    let s' : ZMod q := ↑s
    have : s' ^ p = 1 := by
      unfold s'
      have : (s : ZMod q) ^ p = ↑(s ^ p) := by norm_cast
      rw [this, show (1 : ZMod q) = ↑(1 : ℕ) by norm_cast]
      apply ZMod.eq_iff_modEq_nat q |>.mpr
      exact h_s_pow_p_modeq_1

    -- Let $t$ be the smallest positive integer which satisfies $s^{t} \equiv 1(\bmod q)
    -- (t$ is the order of $s(\bmod q)$ ).
    let t := orderOf s'

    -- One can easily prove that $t$ divides $p$.
    have h_t_dvd_p : t ∣ p := by
      exact orderOf_dvd_of_pow_eq_one this

    -- This means that $t=1$ or $t=p$.
    have h_t_eq_or : t = 1 ∨ t = p := by exact (Nat.dvd_prime hp).mp h_t_dvd_p

    -- However, $t=1$ is easily seen to give a contradiction since then we would have
    -- $$ m(n+1) \equiv 1 \quad(\bmod q) \quad \text { or } \quad n+1 \equiv n \quad(\bmod q) $$
    have h_t_ne_1 : t ≠ 1 := by
      intro h_order_eq_one
      have : s' = 1 := by exact orderOf_eq_one_iff.mp h_order_eq_one
      have : s ≡ 1 [MOD q] := by
        apply ZMod.eq_iff_modEq_nat q |>.mp
        norm_cast
      unfold s at this
      have : m * (n + 1) * n ≡ 1 * n [MOD q] := by exact Nat.ModEq.mul this rfl
      rw [show m * (n + 1) * n = (m * n) * (n + 1) by ring] at this
      have : n + 1 ≡ n [MOD q] := by
        symm
        trans 1 * n
        · congr; ring
        trans (m * n) * (n + 1)
        · exact (Nat.ModEq.symm this)
        trans 1 * (n + 1)
        · apply Nat.ModEq.mul_right
          rwa [mul_comm]
        congr; ring
      have : (q : ℤ) ∣ ↑(n + 1) - n := by
        exact Nat.modEq_iff_dvd.mp (id (Nat.ModEq.symm this))
      simp at this
      norm_cast at this
      have : q = 1 := Nat.eq_one_of_dvd_one this
      have : q > 1 := Nat.Prime.one_lt hq'
      linarith

    -- Therefore $t=p$, and $p$ is the order of $s(\bmod q)$.
    have ht_eq_p : t = p := by simp only [h_t_ne_1, false_or] at h_t_eq_or; assumption

    -- By Fermat's little theorem,
    -- $$ s^{q-1} \equiv 1 \quad(\bmod q) $$
    have : Fact (Nat.Prime q) := by refine { out := hq' }
    have h_s_pow_q_pred_modeq_1 : s' ^ (q - 1) = 1 := by
      refine ZMod.pow_card_sub_one_eq_one ?_
      intro h_s_0
      have : s ≡ 0 [MOD q] := by
        apply ZMod.eq_iff_modEq_nat q |>.mp
        norm_cast
      unfold s at this
      have : q ∣ m * (n + 1) := Nat.dvd_of_mod_eq_zero this
      have : q ∣ m ∨ q ∣ n + 1 := by
        exact (Nat.Prime.dvd_mul hq').mp this
      rcases this with hq_dvd_m | hq_dvd_n_succ
      · have : q ∣ n * m := Dvd.dvd.mul_left hq_dvd_m n
        have : n * m ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr this
        have : 1 ≡ 0 [MOD q] := by
          trans n * m
          exact Nat.ModEq.symm hm
          exact this
        have : q ∣ 1 := Nat.dvd_of_mod_eq_zero this
        have : q = 1 := Nat.eq_one_of_dvd_one this
        have : q > 1 := Nat.Prime.one_lt hq'
        linarith
      · have : ¬ q ∣ n + 1 := by
          refine (Nat.Prime.coprime_iff_not_dvd hq').mp ?_
          exact Nat.coprime_comm.mp h_n_succ_q_gcd_1
        contradiction

    -- Since $p$ is the order of $s(\bmod q)$, we have that $p$ divides $q-1$, and we are done.
    have : t ∣ q - 1 := by exact orderOf_dvd_of_pow_eq_one h_s_pow_q_pred_modeq_1
    rwa [← ht_eq_p]
