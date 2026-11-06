import Mathlib

/- Let $x$ and $y$ be positive integers. If $x^{2^{n}}-1$ is divisible by $2^{n} y+1$ for every positive integer $n$, prove that $x=1$. -/
theorem number_theory_24224 (x y:ℤ)(xpos: 0 < x)(ypos: 0 < y):
  (∀ (n : ℕ), n > 0 → (2^n * y + 1) ∣ (x^(2^n) - 1)) → x = 1 := by
  -- first we prove the following lemma: for every positive odd integer y1, exists infinitely many prime numbers p ≡ 3 (mod 4) and p divide numbers of the form 2^n * y1 + 1. "infinitely many" means such p is unbounded.
  have lemma_aux'(u:ℤ)(y1:ℤ)(y1pos: 0 < y1)(y1odd: Odd y1):
    ∃p:ℤ, Prime p ∧ p > u ∧
    p ≡ 3 [ZMOD 4] ∧ ∃n:ℕ, (0 < n ∧ p ∣ (2^n * y1 + 1)) := by
    by_contra! hcon
    -- suppose on the contrary, then only finitely many primes satisfy
    -- p ≡ 3 (mod 4) and divide (2^n*y+1), i.e., p has upperbound.
    have ex_ub: ∀p:ℤ, (Prime p ∧ p ≡ 3 [ZMOD 4] ∧
      ∃n:ℕ, (0 < n ∧ p ∣ (2^n * y1 + 1))) → p ≤ u := by
      intro p hp
      by_contra! not_ex_ub
      rcases (hp.right.right) with ⟨n, ⟨npos, dvn⟩ ⟩
      have not_dvn := hcon p hp.left not_ex_ub hp.right.left n npos
      apply not_dvn dvn
    -- therefore, only finitely many primes ≡ 3 (mod 4), divide (2^n*y+1) and do not divde 2y+1
    have ex_fin_dv_ndv: ∀p:ℤ, (Prime p ∧ p ≡ 3 [ZMOD 4] ∧
      (∃n:ℕ, 0 < n ∧ p ∣ (2^n*y1+1)) ∧ ¬ (p ∣(2*y1+1))) → p ≤ u := by
      intro p hp
      apply ex_ub p ⟨hp.left, hp.right.left, hp.right.right.left⟩
    -- let's consider factorization of 2y+1 and 2^n * y + 1. suppose 2y+1 = p1^e1 * p2^e2 * ... * pr^er
    -- and those divide some 2^n * y + 1 but do not divide 2y+1 are p_{r+1}, p_{r+2},...,p_{r+s}
    have ex_finset_dv_ndv: ∃s: Finset ℤ, s = {p:ℤ | 0 < p ∧ Prime p ∧
      p ≡ 3 [ZMOD 4] ∧ (∃n:ℕ, 0 < n ∧ p ∣ (2^n*y1+1)) ∧ ¬ (p ∣(2*y1+1))}
      := by
      refine Set.Finite.exists_finset_coe ?h
      rw [Set.finite_iff_bddBelow_bddAbove]
      constructor
      · rw [BddBelow, lowerBounds]; use 0; simp
        intro p hp _ _ _ _ _ _; apply le_of_lt hp
      · rw [BddAbove, upperBounds]; use u; simp
        intro p _ hp1 hp2 n hp3 hp4 hp5
        refine ex_fin_dv_ndv p ⟨hp1, hp2, ?_, hp5⟩
        use n
    -- pset1 = p1,p2,...,pr
    let pset1 := Nat.primeFactors (2*y1+1).toNat
    have pset1_def: pset1 = Nat.primeFactors (2*y1+1).toNat := rfl
    -- notice that 2y1+1 is odd, so prime factors of 2y1+1 must be odd, therefore the product is also odd.
    -- to show prime factors of 2y1+1 is odd, we prove following lemma beforehand. if every member of a finite set is odd, then product is also odd.
    have lemma_prod_odd_nat(s: Finset ℕ)(mem_odd: ∀x ∈ s, Odd x):
      Odd (∏ i ∈ s, i) := by
      induction' s using Finset.induction_on with a s ans ih
      · simp
      · rw [Finset.prod_insert ans]
        apply Nat.odd_mul.mpr
        constructor
        · apply mem_odd a; apply Finset.mem_insert_self a s
        · apply ih; refine fun x a' => mem_odd x ?_
          exact Finset.mem_insert_of_mem a'
    have lemma_prod_odd_int(s: Finset ℤ)(mem_odd: ∀x ∈ s, Odd x):
      Odd (∏ i ∈ s, i) := by
      induction' s using Finset.induction_on with a s ans ih
      · simp
      · rw [Finset.prod_insert ans]
        apply Int.odd_mul.mpr
        constructor
        · apply mem_odd a; apply Finset.mem_insert_self a s
        · apply ih; refine fun x a' => mem_odd x ?_
          exact Finset.mem_insert_of_mem a'
    have pset1_prod_odd: Odd (∏ i ∈ pset1, i) := by
      apply lemma_prod_odd_nat
      rw [pset1_def]; simp; intro p _ pdv _
      refine Odd.of_dvd_nat ?_ pdv
      apply (Int.odd_coe_nat (2*y1+1).toNat).mp
      rw [Int.toNat_of_nonneg (by linarith [ypos])]
      apply odd_two_mul_add_one y1
    --pset2 = p_{r+1},...,p_{r+s}
    rcases ex_finset_dv_ndv with ⟨pset2,pset2_def⟩
    -- since members of pset2 all ≡ 3 (mod 4), so they are odd, and their product also odd.
    have pset2_prod_odd: Odd (∏ i ∈ pset2, i) := by
      apply lemma_prod_odd_int
      have: ∀x ∈ pset2.toSet, Odd x := by
        intro p; rw [pset2_def]; simp; intro _ _ pmod4 _ _ _ _
        refine Int.odd_iff.mpr ?_
        have: 2 ∣ p - 1 := by
          have: p-1 = p-3 + 2 := by ring
          rw [this]
          apply dvd_add_self_right.mpr
          refine Int.dvd_trans ?_ (Int.dvd_sub_of_emod_eq pmod4); norm_num
        apply (Int.modEq_of_dvd this).symm
      apply fun x a => this x a
    -- let's consider p1^(e1+1) * p2^(e2+1) * ... * pr^(er+1) * p_{r+1} * ... * p_{r+s} = (2y+1) * p1 * p2 * ... * p_{r+s}
    let p_prod : ℤ := (∏ i ∈ pset1, i) * (∏ i ∈ pset2, i)
    -- by definition, members in pset1, pset2 are all positive. and their product are also positive. members in pset1, pset2 are odd, so p_prod is also odd.
    have p_prod_def: p_prod = (∏ i ∈ pset1, i) * (∏ i ∈ pset2, i) := rfl
    have p_prod_pos: 0 < p_prod := by
      have: 0 < (∏ i ∈ pset2, i) := by
        apply Finset.prod_pos
        have: ∀ i ∈ pset2.toSet, 0 < i := by
          rw [pset2_def]; simp; intro i ipos; tauto
        apply fun i a => this i a
      refine Int.mul_pos ?_ this
      apply Int.ofNat_pos.mpr
      apply Finset.prod_pos; rw [pset1_def]; simp; intro i pi
      simp [Nat.Prime.pos pi]
    have p_prod_odd: Odd p_prod := by
      rw [p_prod_def]
      refine Int.odd_mul.mpr ?_
      constructor
      · exact (Int.odd_coe_nat (∏ i ∈ pset1, i)).mpr pset1_prod_odd
      · exact pset2_prod_odd
    -- we can find n such that 2^n * y1 + 1 modeq 2*y1 + 1
    have exn_modeq: ∃n:ℕ, n ≥ 2 ∧ 2^n * y1 + 1 ≡ 2*y1 + 1
      [ZMOD (p_prod * (2*y1+1))] := by
      -- this congruence means prime factors of (2y1+1) p1,p2,...,pr "exactly divide" 2^n * y1 + 1, and p_{r+1},...,p_{r+s} not divide 2^n * y1 + 1.
      -- to get such n, recall that Fermat-Euler totient theorem says, if x and n are coprime, then x^(φ n) ≡ 1 mod n
      let m := (p_prod*(2*y1+1)).toNat
      have m_def: m = (p_prod*(2*y1+1)).toNat := rfl
      have m_def': m = p_prod*(2*y1+1) := by
        have: 0 < p_prod*(2*y1+1) := by
          apply Int.mul_pos p_prod_pos (by linarith [ypos])
        rw [m_def]; simp [le_of_lt this]
      have mge3: m ≥ 3 := by
        rw [m_def]; simp
        have ht1: 2*y1+1 ≥ 3 := by linarith [ypos]
        have ht2: p_prod ≥ 1 := by linarith [p_prod_pos]
        refine (Int.le_toNat ?_).mpr ?_
        · linarith [ht1,ht2]
        · simp; rw [← mul_one 3, mul_comm 3 1]
          apply Int.mul_le_mul ht2 ht1 (by norm_num) (le_of_lt p_prod_pos)
      have mtge: m.totient ≥ 1 := by
        rw [Nat.totient]; simp
        use m-1; simp
        constructor
        · linarith [mge3]
        · have : 1 ≤ m := by linarith [mge3]
          apply (Nat.coprime_self_sub_right this).mpr (Nat.gcd_one_right m)
      have two_m_coprime: Nat.Coprime 2 m := by
        have: Nat.Prime 2 := by norm_num
        refine Nat.coprime_two_left.mpr ?_
        have: Odd (m:ℤ) := by
          rw [m_def']
          apply Int.odd_mul.mpr ⟨p_prod_odd, odd_two_mul_add_one y1⟩
        exact (Int.odd_coe_nat m).mp this
      have Fermat_Euler_theorem: 2^(m.totient) ≡ 1 [MOD m] :=
        Nat.ModEq.pow_totient two_m_coprime
      -- 2^(φm) ≡ 1 (mod m), so 2^(φm+1)y+1 ≡ 2^φm 2y + 1 ≡ 2y+1 (mod m)
      use (m.totient+1)
      have ht1: 2^(m.totient+1)*y1 ≡ 2*y1 [ZMOD m] := by
        have h1: 2^(m.totient+1)*y1 = 2^m.totient * (2*y1) := by
          ring
        have h2: 2^m.totient ≡ 1 [ZMOD m] := by
          symm; apply Int.modEq_of_dvd
          have: m ∣ (2^m.totient - 1) := by
            have: 1 ≤ 2^m.totient := Nat.one_le_two_pow
            apply (Nat.modEq_iff_dvd' this).mp Fermat_Euler_theorem.symm
          have := Int.ofNat_dvd.mpr this
          simp at this; exact this
        rw [h1]; nth_rw 2 [← one_mul (2*y1)]
        exact Int.ModEq.mul h2 rfl
      rw [← m_def']
      constructor; linarith [mtge]
      apply Int.ModEq.add ht1 rfl
    rcases exn_modeq with ⟨n, ⟨nge2, modeq1⟩⟩
    have npos: 0 < n := by linarith [nge2]
    -- therefore (2*y1+1) is a factor of 2^n * y1 + 1
    have hdvd1: (2*y1+1) ∣ 2^n * y1 + 1 := by
      have ht1: p_prod * (2*y1 + 1) ∣ (2^n*y1 + 1) - (2*y1+1) := by
        apply Int.ModEq.dvd modeq1.symm
      have ht2: (2*y1+1) ∣ (2^n * y1 + 1) - (2*y1+1) := by
        apply dvd_of_mul_left_dvd ht1
      apply dvd_sub_self_right.mp ht2
    -- and other prime factors of 2^n * y1 + 1, mod 4 eq 1. because we choose such n that those mod 4 eq 3 primes not divide 2^n * y1 + 1
    have pfac_mod4eq1(p:ℤ)(pp: Prime p)(ppos: 0 < p): p ∣ (2^n * y1 + 1) →
      (¬ p ∣ (2*y1+1)) → p ≡ 1 [ZMOD 4] := by
      intro pdv pndv
      -- prime factors of 2^n * y + 1 cannot be even
      have podd: Odd p := by
        have: Odd (2^n * y1 + 1) := by
          have: 2^n * y1 + 1 = 2*(2^(n-1)*y1) + 1 := by
            have: n = n-1 + 1 := by
              have: 1 ≤ n := by linarith [nge2]
              simp [this]
            nth_rw 1 [this]; ring
          rw [this]; exact odd_two_mul_add_one (2^(n-1) * y1)
        rcases pdv with ⟨d,hd⟩; rw [hd] at this
        exact Int.Odd.of_mul_left this
      -- therefore mod 4 eq 3 or eq1.
      have eq1_or_eq3: p ≡ 1 [ZMOD 4] ∨ p ≡ 3 [ZMOD 4] := by
        have h1: p % 2 = 1 := by
          exact Int.odd_iff.mp podd
        rw [Int.emod_def] at h1
        have h2: p = 1 + 2*(p/2) := by linarith [h1]
        rw [h2]
        by_cases pdiv2: p/2 ≡ 1 [ZMOD 2]
        · right
          have hh1: 2 * (p/2) ≡ 2*1 [ZMOD 2*2] := by
            exact Int.ModEq.mul_left' pdiv2
          have hh2: (3:ℤ) = 1 + 2 := by norm_num
          simp at hh1; rw [hh2]
          apply Int.ModEq.add (by norm_num) hh1
        · left
          have hh1: p/2 ≡ 0 [ZMOD 2] := by
            rcases (Int.emod_two_eq (p/2)) with mod2e0 | mod2e1
            · apply mod2e0
            · exfalso; apply pdiv2 mod2e1
          have hh2: 2 * (p/2) ≡ 2*0 [ZMOD 2*2] := by
            exact Int.ModEq.mul_left' hh1
          simp at hh2; nth_rw 2 [← add_zero 1]
          apply Int.ModEq.add (by norm_num) hh2
      rcases eq1_or_eq3 with pe1 | pe3
      · apply pe1
      -- if p ≡ 3 (mod 4), then p ∈ pset2, therefore we can prove p not divide 2^n * y1 + 1, reach a contradiction.
      · have p_in_set2: p ∈ pset2 := by
          have ht1: p ∈ pset2.toSet := by
            rw [pset2_def]; simp
            refine ⟨ppos, pp, pe3, ?_, pndv⟩; use n
          apply ht1
        have hdvsub: p ∣ (2^n * y1 + 1) - (2*y1+1) := by
          have ht1: p_prod ∣ (2^n * y1 + 1) - (2*y1 + 1) := Int.dvd_trans
            (Int.dvd_mul_right p_prod (2*y1+1))
            (Int.ModEq.dvd modeq1.symm)
          have ht2: p ∣ p_prod := by
            rw [p_prod_def]
            apply Dvd.dvd.mul_left
              (Finset.dvd_prod_of_mem id p_in_set2) ↑(∏ i ∈ pset1, i)
          apply Int.dvd_trans ht2 ht1
        have hdv: p ∣ 2*y1+1 := by
          apply (Int.dvd_iff_dvd_of_dvd_sub hdvsub).mp pdv
        exfalso; apply pndv hdv
    have modeq2: 2^n * y1 + 1 ≡ 2*y1 + 1 [ZMOD 4] := by
      -- 2^n * y + 1 consists of prime powers, and they mod 4 eq 1.
      rcases hdvd1 with ⟨facs, hfacs⟩
      -- we prove prime factors of (2^n * y1 + 1)/(2y1+1) are those divide 2^n * y1 + 1 but not divide 2y1+1 factors, therefore mod 4 eq 1. and thus facs self mod 4 eq 1.
      have fpos: 0 < facs := by
        have h1: 0 < 2^n * y1 + 1 := by
          have: 0 < 2^n * y1 := by
            refine Int.mul_pos ?_ y1pos
            apply pow_pos (by norm_num)
          linarith [this]
        have h2: 0 < 2*y1 + 1 := by linarith [ypos]
        rw [hfacs] at h1
        exact (pos_iff_pos_of_mul_pos h1).mp h2
      have facs_m4e1: facs ≡ 1 [ZMOD 4] := by
        -- simplify at modeq1
        have facs_mod_prod_e1: facs ≡ 1 [ZMOD p_prod] := by
          rw [hfacs] at modeq1; nth_rw 3 [← mul_one (2*y1+1)] at modeq1
          have h1: Int.gcd (p_prod*(2*y1+1)) (2*y1+1) = 2*y1+1 := by
            symm
            refine Int.gcd_greatest ?_ ?_ ?_ fun e _ a => a
            · linarith [y1pos]
            · exact Int.dvd_mul_left p_prod (2*y1 + 1)
            · exact Int.dvd_refl (2 * y1 + 1)
          have h2: 0 < p_prod*(2*y1+1) := by
            apply Int.mul_pos p_prod_pos (by linarith [y1pos])
          have h3: p_prod = (p_prod*(2*y1+1)) /
            Int.gcd (p_prod*(2*y1+1)) (2*y1+1) := by
            rw [h1]; refine (Int.mul_ediv_cancel _ ?_).symm; linarith
          rw [h3]
          apply Int.ModEq.cancel_left_div_gcd h2 modeq1
        -- therefore facs and p_prod are coprime. for any prime factors p of facs, p is coprime with elements from pset1, therefore not divide 2*y1+1.
        have pfacs_ndv: ∀p:ℤ, 0 < p ∧ Prime p ∧ p ∣ facs →
          ¬ p ∣ 2*y1+1 := by
          intro p ⟨ppos, pprime, pdvf⟩
          -- facs ≡ 1 (mod p_prod) means that facs and p_prod are coprime, or p_prod divide facs-1
          obtain hdvd1 := Int.ModEq.dvd facs_mod_prod_e1.symm
          -- and if p ∣ 2y1+1, then p ∣ p_prod. because p_prod contain prime factors from 2y1+1
          by_contra! pdv2y1
          have hdvd2: p ∣ p_prod := by
            obtain pn := (Int.toNat_of_nonneg (le_of_lt ppos)).symm
            have h2y1n: 2*y1+1 = ↑(2*y1+1).toNat := by
              refine (Int.toNat_of_nonneg ?_).symm; linarith
            rw [pn] at pprime pdv2y1; rw [h2y1n] at pdv2y1
            refine Dvd.dvd.mul_right ?_ _
            rw [pn]; refine Int.ofNat_dvd.mpr ?_
            have: p.toNat ∈ pset1 := by
              refine Nat.mem_primeFactors.mpr ?_; constructor
              · apply Nat.prime_iff_prime_int.mpr pprime
              · exact ⟨Int.ofNat_dvd.mp pdv2y1, (by linarith [y1pos])⟩
            apply Finset.dvd_prod_of_mem _ this
          -- but facs and 2y1+1 are coprime, p cannot divide both. therefore we get a contradiction.
          obtain hdvd3 := (Int.dvd_iff_dvd_of_dvd_sub
            (Int.dvd_trans hdvd2 hdvd1)).mp pdvf
          apply Prime.not_dvd_one pprime hdvd3
        -- we already prove if p divide 2^n y1+1 but not divide 2y1+1, then p ≡ 1 (mod 4). so prime factors of facs mod 4 eq 1.
        have pfacs_m4e1: ∀p:ℤ, 0 < p ∧ Prime p ∧ p ∣ facs →
          p ≡ 1 [ZMOD 4] := by
          intro p ⟨ppos, pprime, pdv⟩
          refine pfac_mod4eq1 p pprime ppos ?_ ?_
          · apply Int.dvd_trans pdv (Dvd.intro_left (2*y1+1) hfacs.symm)
          · apply pfacs_ndv p ⟨ppos, pprime, pdv⟩
        -- and we need the following lemma: if all prime factors of an integer mod eq 1, then that integer self mod eq 1.
        have lemma_modeq1_of_pfacs_modeq1'(a b:ℕ)(ha: 0 < a)
          (h: ∀p:ℕ, (0 < p ∧ Nat.Prime p ∧ p ∣ a) → p ≡ 1 [MOD b]):
          a ≡ 1 [MOD b] := by
          -- notice that for any natural number a, a can be written in the form a = p1^e1 * p2^e2 * ... * pn^en
          rw [← Nat.factorization_prod_pow_eq_self ha.ne']
          rw [Nat.prod_factorization_eq_prod_primeFactors]
          have h1(p:ℕ)(ppos: 0 < p)(pp: Nat.Prime p)(pdva: p ∣ a):
            ∀n:ℕ, p^n ≡ 1 [MOD b] := by
            intro n
            induction' n with d hd
            · simp; rfl
            · rw [pow_succ, ← mul_one 1]
              apply Nat.ModEq.mul hd (h p ⟨ppos, pp, pdva⟩)
          have h2: ∀p ∈ a.primeFactors,
            p^(a.factorization p) ≡ 1 [MOD b] := by
            intro p hp
            refine h1 p ?_ ?_ ?_ (a.factorization p)
            · exact Nat.pos_of_mem_primeFactors hp
            · exact Nat.prime_of_mem_primeFactors hp
            · exact Nat.dvd_of_mem_primeFactors hp
          induction' a.primeFactors using Finset.induction_on
            with q s qns ih
          · simp; rfl
          · rw [Finset.prod_insert qns, ← mul_one 1]
            apply Nat.ModEq.mul
            · by_cases hq: q ∈ a.primeFactors
              · apply h2 q hq
              · rw [Finsupp.not_mem_support_iff.mp hq]; simp; rfl
            · apply ih
        -- and following is the same lemma for integer. basically, positive integer and (positive) natural number share same rules.
        have lemma_modeq1_of_pfacs_modeq1(a b:ℤ)(ha: 0 < a)(hb: 0 < b):
          (∀p:ℤ, ((0 < p ∧ Prime p ∧ p ∣ a) → p ≡ 1 [ZMOD b])) →
          a ≡ 1 [ZMOD b] := by
          intro h
          have h1: (1:ℤ) = ↑(1:ℕ) := by simp
          have h2: ↑a.toNat = a := Int.toNat_of_nonneg (le_of_lt ha)
          have h3: ↑b.toNat = b := Int.toNat_of_nonneg (le_of_lt hb)
          rw [h1, ← h2, ← h3]
          apply Int.natCast_modEq_iff.mpr
          apply lemma_modeq1_of_pfacs_modeq1'
          · apply Int.ofNat_pos.mp; rwa [← h2] at ha
          · intro p hp
            apply Int.natCast_modEq_iff.mp
            rw [h3]; simp
            refine h p ⟨?_, ?_, ?_⟩
            · exact Int.ofNat_pos.mpr hp.left
            · exact Nat.prime_iff_prime_int.mp hp.right.left
            · rw [← h2]
              exact Int.ofNat_dvd.mpr hp.right.right
        -- equipped with those lemma, we can prove since prime factors of facs all mod 4 eq 1, facs self ≡ 1 (mod 4)
        apply lemma_modeq1_of_pfacs_modeq1 facs 4
          fpos (by norm_num) pfacs_m4e1
      rw [hfacs]; nth_rw 2 [← mul_one (2*y1+1)]
      apply Int.ModEq.mul_left _ facs_m4e1
    -- now, let's calculate 2^n * y1 + 1 mod 4 and 2y1+1 mod 4.
    have left_modeq: 2^n * y1 + 1 ≡ 1 [ZMOD 4] := by
      -- n ≥ 2, so 4 ∣ 2^n ,and 2^n * y1 + 1 ≡ 1 (mod 4)
      have h1: 4 ∣ 2^n * y1 := by
        have: (2^n:ℤ) = 4*(2^(n-2)) := by
          have: n = 2+(n-2) := by simp [nge2]
          nth_rw 1 [this]; ring
        rw [this, mul_assoc]; apply Int.dvd_mul_right 4 _
      rcases h1 with ⟨e,he⟩
      rw [he, add_comm]
      apply Int.modEq_add_fac_self
    -- however, when y1 is odd, 2y1+1 mod 4 is 3.
    have right_modeq: 2*y1 + 1 ≡ 3 [ZMOD 4] := by
      have h1: y1 ≡ 1 [ZMOD 2] := by
        apply Int.odd_iff.mp y1odd
      have h2: 2*y1 ≡ 2*1 [ZMOD 2*2] := by
        apply Int.ModEq.mul_left' h1
      simp at h2; apply Int.ModEq.add h2 rfl
    -- thereby we get a contradiction
    have contra: 1 ≡ 3 [ZMOD 4] := Int.ModEq.trans
      (Int.ModEq.trans left_modeq.symm modeq2) right_modeq
    contradiction
  -- thus we prove a key lemma for this problem.
  -- however, we suppose y1 to be odd just now. in fact, if odd case holds, then y even case holds too. so it simplifies to the following.
  have lemma_aux: ∀u:ℤ, ∃p:ℤ, Prime p ∧ p > u ∧
    p ≡ 3 [ZMOD 4] ∧ ∃n:ℕ, 0 < n ∧ p ∣ 2^n * y + 1 := by
    intro u
    by_cases parity_y: Even y
    · have nynz: y.toNat ≠ 0 := by
        have h1: y = y.toNat := by
          symm; apply Int.toNat_of_nonneg (le_of_lt ypos)
        have h2: y ≠ 0 := ypos.ne'
        rw [h1] at h2
        exact fun a => h2 (congrArg Nat.cast a)
      have ynpos: 0 < y.toNat := by
        exact Nat.zero_lt_of_ne_zero nynz
      -- take factor 2 out of y, thus exists k,y1, 2^k*y1 =y, and y1 is odd.
      obtain ⟨k,y1,⟨oddy1,hy1⟩⟩ := Nat.exists_eq_two_pow_mul_odd nynz
      have y1pos: 0 < y1 := by
        rw [hy1] at ynpos
        apply Nat.pos_of_mul_pos_left ynpos
      have y1pos': (0:ℤ) < ↑y1 := Int.ofNat_pos.mpr y1pos
      have oddy1': Odd (y1:ℤ) := (Int.odd_coe_nat y1).mpr oddy1
      have y_of_k: y = 2^k * ↑y1 := by
        have: y = y.toNat := by
          symm; apply Int.toNat_of_nonneg (le_of_lt ypos)
        rw [this, hy1]; simp
      -- notice that n can be very large. in case that we could have 2^n = 2^(n-k)*2^k, we should choose a sufficiently large lowerbound for p.
      let u' := max u (2^k * y1 + 1)
      have u'_def: u' = (max u (2^k * y1 + 1)) := rfl
      rcases lemma_aux' u' y1 y1pos' oddy1' with
        ⟨p, ⟨pp, pgt, pmod4eq3, exn⟩ ⟩
      have pgt': p > u := by
        refine Int.lt_of_le_of_lt ?_ pgt
        rw [u'_def]; exact Int.le_max_left u (2^k * ↑y1 + 1)
      use p; refine ⟨pp, pgt', pmod4eq3, ?_⟩; rw [y_of_k]
      rcases exn with ⟨n1, ⟨_, hn1⟩ ⟩; use (n1-k)
      -- by choosing large u', we can show k ≤ n1.
      have kltn: k < n1 := by
        have h1: (2:ℤ)^k * y1 + 1 < 2^n1 * y1 + 1 := by
          have hh1: p ≤ 2^n1 * y1 + 1 := by
            apply Int.le_of_dvd
            · have: 0 < (2:ℤ)^n1 * y1 := by
                refine Int.mul_pos ?_ y1pos'
                apply pow_pos (by norm_num)
              linarith [this]
            · apply hn1
          have hh2: (2:ℤ)^k * y1 + 1 < p := by
            refine lt_of_le_of_lt ?_ pgt
            rw [u'_def]; apply Int.le_max_right
          apply lt_of_lt_of_le hh2 hh1
        have h2: (1:ℤ) < 2 := by norm_num
        simp only [add_lt_add_iff_right] at h1
        apply (pow_lt_pow_iff_right₀ h2).mp
        exact (zsmul_lt_zsmul_iff_left y1pos').mp h1
      -- therefore 2^n1 = 2^(n1-k) 2^k, so 2^(n1-k) witness exists n', p divide 2^n' (2^ky1) + 1
      have: (2:ℤ)^n1 = 2^(n1-k)*2^k := by
        rw [← pow_add]; congr
        exact (Nat.sub_eq_iff_eq_add kltn.le).mp rfl
      constructor; exact Nat.zero_lt_sub_of_lt kltn
      rwa [this, mul_assoc] at hn1
    · -- odd case we already proved.
      have yodd: Odd y := Int.not_even_iff_odd.mp parity_y
      have := lemma_aux' u y ypos yodd
      tauto
  -- finish proving those two lemma, let's proceed to the problem.
  -- if p is a prime divisor of2^ny+1, by the problem statement, p also divide x^(2^n), or x^(2^n) ≡ 1 (mod p). fermat little theorem says x^(p-1) ≡ 1 (mod p), so x^(gcd(2^n,p)) ≡ 1 (mod p). and that gcd is 2, so x^2 ≡ 1 (mod p), or p ∣ x^2-1
  intro hdvd
  have p_dvd_x21(p:ℤ)(ppos:0<p)(prime_p: Prime p)(pmod4: p ≡ 3 [ZMOD 4]):
    (∃n:ℕ, 0 < n ∧ p ∣ (2^n * y + 1)) → p ∣ (x^2-1) := by
    -- if x^m ≡ 1 mod p and x^n ≡ 1 mod p, then x^(gcd(m,n)) ≡ 1 mod p.
    have lemma_gcd_mod: ∀(m n:ℕ), 0 < n →
      (x^m ≡ 1 [ZMOD p] ∧ x^n ≡ 1 [ZMOD p]) →
      x^(m.gcd n) ≡ 1 [ZMOD p] := by
      intro m n npos ⟨hm,hn⟩
      have h1: m.gcd n ≤ n := Nat.gcd_le_right n npos
      by_cases hnn: m.gcd n = n
      · rw [hnn]; apply hn
      · obtain ⟨d,hd⟩ := Nat.exists_mul_emod_eq_gcd
          (Nat.lt_of_le_of_ne h1 hnn)
        rw [Nat.mod_def] at hd; rw [← hd]
        have h2: x^(m*d-n*(m*d/n)) = x^(m*d) / x^(n*(m*d/n)) := by
          refine Int.eq_ediv_of_mul_eq_right ?_ ?_
          · apply pow_ne_zero _ xpos.ne'
          · rw [← pow_add]; congr
            rw [← Nat.add_sub_assoc (Nat.mul_div_le _ _), add_comm]
            rw [Nat.add_sub_assoc (le_refl _)]; simp
        have h3: (x^n)^(m*d/n) ≡ 1 [ZMOD p] := by
          have: (1:ℤ) = 1^(m*d/n) := by ring
          rw [this]; apply Int.ModEq.pow _ hn
        have h4: x^(m*d-n*(m*d/n)) * x^(n*(m*d/n)) ≡ x^(m*d) [ZMOD p]
          := by
          rw [h2]; congr
          apply Int.ediv_mul_cancel
          apply pow_dvd_pow x (Nat.mul_div_le (m*d) n)
        have h5: x^(m*d-n*(m*d/n)) ≡ x^(m*d) [ZMOD p] := by
          refine Int.ModEq.trans ?_ h4
          have: x^(n*(m*d/n)) = (x^n)^(m*d/n) := by ring
          rw [this]
          nth_rw 1 [← mul_one (x^(m*d-n*(m*d/n)))]
          apply Int.ModEq.mul_left _ h3.symm
        have h6: x^(m*d) ≡ 1 [ZMOD p] := by
          have hh1: (1:ℤ) = 1^d := by ring
          have hh2: x^(m*d) = (x^m)^d := by ring
          rw [hh1, hh2]
          exact Int.ModEq.pow d hm
        exact Int.ModEq.trans h5 h6
    intro ⟨n, hn, hpdv0⟩
    have hmod1: x^(2^n) ≡ 1 [ZMOD p] := by
      -- from the problem statement (hdvd), 2^n * y + 1 ∣ x^(2^n)-1. so if divides the former, then p also divides the latter.
      have h1: p ∣ x^(2^n) - 1 := Int.dvd_trans hpdv0 (hdvd n hn)
      symm; apply Int.modEq_iff_dvd.mpr h1
    let p' := (p-1).toNat
    have p'_def: p' = (p-1).toNat := rfl
    -- by Fermat's little theorem, if p does not divde x, then x^(p-1) ≡ 1 (mod p)
    have hmod2: x^p' ≡ 1 [ZMOD p] := by
      -- x^(2^n) ≡ 1 (mod p), so p and x must be coprime.
      have cop_xp: IsCoprime x p := by
        symm; apply (Prime.coprime_iff_not_dvd prime_p).mpr
        by_contra! pdvx
        have pdvx2n: p ∣ x^(2^n) := by
          apply Int.dvd_trans pdvx
          apply dvd_pow_self x (pow_ne_zero _ (by norm_num))
        have pdv1: p ∣ 1 := (Int.dvd_iff_dvd_of_dvd_sub
          (Int.ModEq.dvd hmod1.symm)).mp pdvx2n
        apply Prime.not_dvd_one prime_p pdv1
      -- thus we can use fermat little theorem.
      have := Int.toNat_of_nonneg (le_of_lt ppos)
      rw [← this] at prime_p cop_xp
      have fermat_little := Int.ModEq.pow_card_sub_one_eq_one
        (Nat.prime_iff_prime_int.mpr prime_p) cop_xp
      simp at p'_def; rw [← p'_def] at fermat_little
      rwa [this] at fermat_little
    -- apply the lemma, let d = (2^n,p') (gcd of 2^n and p'), then x^d ≡ 1 (mod p)
    let d := (2^n).gcd p'
    have d_def: d = (2^n).gcd p' := rfl
    have p'pos: 0 < p' := by
      rw [p'_def]; simp;
      apply lt_of_le_of_ne ppos (Prime.ne_one prime_p).symm
    have hmod3: x^d ≡ 1 [ZMOD p] := by
      apply lemma_gcd_mod (2^n) p' p'pos ⟨hmod1, hmod2⟩
    -- and p ≡ 3 (mod 4), so gcd of 2^n and p' is 2.
    have deq: d = 2 ∨ n = 0 := by
      have h1: p' ≡ 2 [ZMOD 4] := by
        refine Int.ModEq.add_right_cancel' 1 ?_
        rw [p'_def, Int.toNat_of_nonneg (by linarith [ppos])]
        simp; exact pmod4
      have h2: p' ≡ 2 [MOD 4] := Nat.modEq_of_dvd (Int.ModEq.dvd h1)
      -- p' ≡ 2 (mod 4), so p' ≥ 2. and 2 divide p' but 4 not divide p'
      have h3: 2 ∣ p' := by
        refine (Nat.ModEq.dvd_iff h2.symm ?_).mp ?_
        · norm_num
        · simp
      have h5: ¬ 4 ∣ p' := by
        by_contra! hc
        have: 2 ≡ 0 [MOD 4] := by
          symm; refine Nat.ModEq.trans ?_ h2
          symm; apply Nat.modEq_zero_iff_dvd.mpr hc
        contradiction
      -- if c divide 2^n, then it must have the form of 2^m
      have hdv2n(c:ℕ): c ∣ 2^n → ∃m:ℕ, c = 2^m := by
        intro cdv
        have p2: Nat.Prime 2 := by norm_num
        have := (Nat.dvd_prime_pow p2).mp cdv
        tauto
      rw [d_def, Nat.gcd_eq_iff]
      -- when n=0, trivially true.
      by_cases hn': n=0
      · tauto
      · -- n ≠ 0, then n ≥ 1
        left
        constructor; exact dvd_pow_self 2 hn'
        constructor; exact h3
        intro c cdv2n cdvp'
        obtain ⟨m, hcm⟩ := hdv2n c cdv2n
        have mle1: m ≤ 1 := by
          by_contra! mgt1
          refine h5 (Nat.dvd_trans ?_ cdvp')
          have: c = 2^(m-2)*4 := by
            rw [hcm]
            have := (Nat.sub_eq_iff_eq_add mgt1).mp rfl
            nth_rw 1 [this]; ring
          rw [this]; apply Nat.dvd_mul_left
        rw [hcm]; interval_cases m; all_goals simp
    -- thus we have x^2 ≡ 1 (mod p)
    have hmod4: x^2 ≡ 1 [ZMOD p] := by
      rcases deq with d2 | n0
      · rw [d2] at hmod3; apply hmod3
      · rw [n0] at hmod1; simp at hmod1
        rw [pow_two, ← mul_one 1]
        exact Int.ModEq.mul hmod1 hmod1
    -- so p ∣ x^2-1
    apply Int.ModEq.dvd (hmod4.symm)
  -- we already prove that if ∃n, p ∣ 2^n y +1 , then p ∣ x^2-1. since there are infinitely many prime p divide 2^n y +1, so also infinitely many p divide x^2-1. but x^2-1 is finite, so x^2-1 can only be 0.
  have xeq': x^2-1 = 0 := by
    by_contra! hc
    have hgt: 0 < x^2-1 := by
      have: 0 ≤ x^2-1 := Int.sub_nonneg_of_le (lt_of_le_of_ne
        (sq_nonneg x) (pow_ne_zero 2 xpos.ne').symm)
      apply lt_of_le_of_ne this hc.symm
    rcases (lemma_aux (x^2-1)) with ⟨p, ⟨pp,pgt,pmod4eq3,exnpdv⟩⟩
    -- by p_dvd_x21, we have p divides x^2-1
    have: p ∣ x^2-1 := by
      have ppos: 0 < p := by linarith [hgt, pgt]
      apply p_dvd_x21 p ppos pp pmod4eq3; tauto
    -- however, p ∣ x^2-1 and x^2-1 ≠ 0, so p ≤ x^2-1.
    have ple: p ≤ x^2-1 := Int.le_of_dvd hgt this
    -- we get a contradiction.
    linarith [ple, pgt]
  -- x^2-1=0, therefore x can only be 1.
  have xeq: x = 1 := by
    have: (x+1) * (x-1) = 0 := by
      rw [← xeq']; ring
    rcases (mul_eq_zero.mp this) with xn1 | xp1
    · exfalso; linarith [xn1, xpos]
    · linarith [xp1]
  exact xeq