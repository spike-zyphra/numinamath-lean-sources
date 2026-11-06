import Mathlib

open Nat Finset

/-Find all positive integers n such that the product of all positive divisors of n is \(n^3\).-/
theorem prod_divisors_eq_n_cube_iff (n : ℕ) (h: n > 0):
  (∏ d ∈ n.divisors, d) = n ^ 3 ↔
    n = 1 ∨
    (∃ p, Nat.Prime p ∧ n = p ^ 5) ∨
    (∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p ^ 2 * q) := by

  have eq_prod_primeFactors : ∀ (m : ℕ), m ≠ 0 → m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
    intro m hm
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact (Nat.factorization_prod_pow_eq_self hm).symm

  have prime_factor_exp_pos :
    ∀ (m : ℕ) (hm : m ≠ 0) (q : ℕ), q ∈ m.primeFactors → 0 < m.factorization q := by
    intro m hm q hq
    -- exactly the same proof as your original lemma, but with `m`, `hm`, `q`, `hq`:
    have h_temp := Nat.mem_primeFactors.1 hq
    have hpp : Nat.Prime q ∧ q ∣ m := ⟨h_temp.1, h_temp.2.1⟩
    exact Prime.factorization_pos_of_dvd hpp.1 (by positivity) hpp.2

  -- Case 1: n = 1
  by_cases h1 : n = 1
  · subst h1
    -- `divisors 1 = {1}`, so `∏ d ∈ divisors 1, d = 1` and `1^3 = 1`.
    simp [Nat.divisors_one, Finset.prod_singleton]

  -- Now n ≠ 1, so in particular `2 ≤ n`.
  have hn : 1 < n := by omega
  have hn2 : 2 ≤ n := by omega

  -- The product of all positive divisors of `n` is `n ^ (d(n)/2)`.
  have prod_divisors_eq_pow_half_card: (∏ d ∈ n.divisors, d)^2 = n ^ (n.divisors.card) := by

    -- Use the identity: ∏ d, n / d = ∏ d, d

    have h_prod : ∏ d ∈ n.divisors, (n / d) = (∏ d ∈ n.divisors, d):= by calc
      _ = ∏ d ∈ n.divisors, (n / d) := by simp
      _ = n.divisors.prod id := Nat.prod_div_divisors n (id : ℕ → ℕ)
      _ = ∏ d ∈ n.divisors, d := by simp

    -- First prove the squared equality
    have hsq : (∏ d ∈ n.divisors, d) ^ 2 = n ^ n.divisors.card := calc
      (∏ d ∈ n.divisors, d) ^ 2
          = (∏ d ∈ n.divisors, d) * (∏ d ∈ n.divisors, d) := by rw [pow_two]
      _   = (∏ d ∈ n.divisors, d) * (∏ d ∈ n.divisors, (n / d)) := by
            rw [h_prod]
      _   = ∏ d ∈ n.divisors, d * (n / d) := by rw [← Finset.prod_mul_distrib]
      _   = ∏ d ∈ n.divisors, n := by
            apply Finset.prod_congr rfl
            intros d hd
            rw [Nat.mul_div_cancel']
            exact Nat.dvd_of_mem_divisors hd
      _   = n ^ n.divisors.card := by rw [Finset.prod_const]

    exact hsq

  -- We build an `iff` chain:
  have h_card : (∏ d ∈ n.divisors, d) = n ^ 3 ↔ ∏ x ∈ n.primeFactors, (n.factorization x + 1) = 6 := by calc
    (∏ d ∈ n.divisors, d) = n ^ 3 ↔ (∏ d ∈ n.divisors, d)^2 = (n ^ 3) ^ 2 := by
      exact (sq_eq_sq₀ (by positivity) (by positivity)).symm
    _ ↔ n ^ (n.divisors.card) = n ^ 6 := by ring_nf; rw [prod_divisors_eq_pow_half_card]
    _ ↔ n.divisors.card = 6 := by exact pow_right_inj₀ h h1
    _ ↔ ∏ x ∈ n.primeFactors, (n.factorization x + 1) = 6 := by rw [Nat.card_divisors (by positivity)]

  rw [h_card]

  have primeFactors_prod_factorization_add_one_eq_six_iff : (∏ i ∈ n.primeFactors, (n.factorization i + 1) = 6)
    ↔ (∃ p, Prime p ∧ n = p ^ 5) ∨ ∃ p q, Prime p ∧ Prime q ∧ p ≠ q ∧ n = p ^ 2 * q := by
    let s := n.primeFactors
    -- `s` is nonempty because `n > 1`.
    have hs_ne : s ≠ ∅ := by
      simp [s, primeFactors_eq_empty]
      omega

    -- Therefore `2 ^ card s ≤ ∏ p ∈ s, n.factorization p + 1`.
    have h_pow_le : 2 ^ s.card ≤ ∏ i ∈ s, (n.factorization i + 1) := by
      have h₀: ∀ i ∈ s, 0 ≤ 2:= by norm_num
      have h₁: ∀ i ∈ s, 2 ≤ n.factorization i + 1:= by
        intro i hi
        have hpos : 0 < n.factorization i := prime_factor_exp_pos n (by positivity) i hi
        omega

      calc _ = ∏ p ∈ s, 2 := by rw [Finset.prod_const 2]
          _ ≤ ∏ p ∈ s, (n.factorization p + 1) := by
            apply Finset.prod_le_prod'
            exact fun i hi => h₁ i hi


    -- Now use the hypothesis `∏ p ∈ s, n.factorization p + 1 = 6` to bound `2 ^ s.card ≤ 6`.

    -- -- By a standard lemma (`pow_le_iff_le_right`), since `1 < 2` and `6 < 2 ^ 3 = 8`,
    -- -- we conclude `s.card ≤ 2`.
    -- have card_le_two : s.card ≤ 2 :=
    --   Nat.pow_le_iff_le_right (by decide : 1 < 2) h_pow_le_six (by norm_num : 6 < 2 ^ 3)

    -- -- Now `s.card ≥ 1` (because `s ≠ ∅`), so `s.card = 1` or `s.card = 2`.
    -- We split into the two possible sizes of `s`.
    constructor
    · intro h_prod

      have h_pow_le_six : 2 ^ s.card ≤ 6 := by calc
        2 ^ s.card ≤ ∏ i ∈ s, (n.factorization i + 1) := by simp [h_pow_le]
                _ = 6 := h_prod

      -- By a standard lemma (`pow_le_iff_le_right`), since `1 < 2` and `6 < 2 ^ 3 = 8`,
      -- we conclude `s.card ≤ 2`.
      have card_le_two : s.card ≤ 2 := by
        by_contra h_not
        push_neg at h_not
        have : 3 ≤ s.card := Nat.succ_le_iff.mpr h_not
        have : 8 ≤ 6 := calc 8 = 2^3 := by norm_num
                            _ ≤ 2^s.card := Nat.pow_le_pow_right (by norm_num) this
                            _ ≤ 6 := h_pow_le_six
        norm_num at this

      have card_cases : s.card = 1 ∨ s.card = 2 := by
        have h_pos : s.card ≠ 0 := fun h => hs_ne (Finset.card_eq_zero.mp h)
        omega

      -- Case 1: `s.card = 1`.
      rcases card_cases with (h1 | h2)
      · -- `s.card = 1`.
        -- Since `n.primeFactors = 1`, we can suppose `n.primeFactors` is a singleton `{p}`. and `∏ i ∈ n.primeFactors, (n.factorization i + 1) = p + 1 = 6`.

        -- there exists a unique prime `p` ∈ `n.primeFactors`

        rcases Finset.card_eq_one.1 h1 with ⟨p₀, h_unique_prime⟩

        have h_exponet: n.factorization p₀ = 5 := by
          have : 6 = n.factorization p₀ + 1:= by
            rw [← h_prod]
            have : n.primeFactors = {p₀} := by
              simpa using h_unique_prime
            simp_rw [this]
            simp_rw [Finset.prod_singleton]
          linarith

        have : p₀ ∈ n.primeFactors := by
          refine singleton_subset_iff.mp ?_
          unfold s at h_unique_prime
          rw[h_unique_prime]
        have h_prime_p₀ : Nat.Prime p₀ := by
          exact (mem_primeFactors.1 this).1



        have : n = p₀ ^ 5 := by
          calc
            n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := eq_prod_primeFactors n (by omega)
            _ = ∏ p ∈ s, p ^ n.factorization p := by rfl
            _ = p₀ ^ n.factorization p₀ := by rw [h_unique_prime, Finset.prod_singleton]
            _ = p₀ ^ 5 := by simp [‹n.factorization p₀ = 5›]

        exact Or.inl ⟨p₀, h_prime_p₀, this⟩

      · -- Case 2: `s.card = 2`.
        -- Enumerate the two distinct primes `p, q`. Because `s.card = 2`, we know `s = {p, q}` with `p ≠ q`.
        obtain ⟨p, q, hp_mem, hq_mem, hpq_ne⟩ :
          ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ s = {p, q} := by
          obtain ⟨p, q, hpq_ne, hs_eq⟩ := Finset.card_eq_two.mp h2
          exact ⟨p, q, by rw [hs_eq]; simp, by rw [hs_eq]; simp, hpq_ne, hs_eq⟩
        -- From `h_prod : ∏ p ∈ {p, q}, n.factorization p + 1 = 6`, we get `(n.factorization p + 1) * (n.factorization q + 1) = 6`.
        have h_prod_eq : (n.factorization p + 1) * (n.factorization q + 1) = 6 := by
          have : ∏ i ∈ {p, q}, (n.factorization i + 1) = 6 := by
            rwa [← hpq_ne.2]
          rwa [Finset.prod_pair hpq_ne.1] at this

        -- Each exponent is ≥ 1, so `(n.factorization p + 1) ≥ 2` and `(n.factorization q + 1) ≥ 2`.
        have hp_ge2 : 2 ≤ n.factorization p + 1 := by
          linarith [prime_factor_exp_pos n (by positivity) p hp_mem]
        have hq_ge2 : 2 ≤ n.factorization q + 1 := by
          linarith [prime_factor_exp_pos n (by positivity) q hq_mem]

        -- The only factorization of `6` into two naturals ≥ 2 is `6 = 2 * 3` or `3 * 2`.
        have mul_cases : (n.factorization p + 1 = 2 ∧ n.factorization q + 1 = 3)
                      ∨ (n.factorization p + 1 = 3 ∧ n.factorization q + 1 = 2) := by
          -- Since (n.factorization p + 1) * (n.factorization q + 1) = 6
          -- and both factors are ≥ 2, we must have them be 2 and 3
          have hp_le3 : n.factorization p + 1 ≤ 3 := by
            by_contra h
            push_neg at h
            have : 4 ≤ n.factorization p + 1 := Nat.succ_le_iff.mpr h
            have : 8 ≤ 6 := calc 8 = 4 * 2 := by norm_num
                              _ ≤ (n.factorization p + 1) * (n.factorization q + 1) := Nat.mul_le_mul this hq_ge2
                              _ = 6 := h_prod_eq
            omega

          have hq_le3 : n.factorization q + 1 ≤ 3 := by
            by_contra h_contr
            push_neg at h_contr
            have : 4 ≤ n.factorization q + 1 := Nat.succ_le_iff.mpr h_contr
            have : 8 ≤ 6 := calc 8 = 2 * 4 := by norm_num
                                _ ≤ (n.factorization p + 1) * (n.factorization q + 1) := Nat.mul_le_mul hp_ge2 this
                                _ = 6 := h_prod_eq
            norm_num at this
          interval_cases n.factorization p + 1; interval_cases n.factorization q + 1
          · -- Case: p+1=2, q+1=2 → 2*2=4≠6, contradiction
            exfalso; linarith [h_prod_eq]
          · -- Case: p+1=2, q+1=3 → 2*3=6 ✓
            left; exact ⟨rfl, rfl⟩
          · -- Case: p+1=3, q+1=2 → 3*2=6 ✓
            right; exact ⟨rfl, by linarith [h_prod_eq]⟩


        -- In each case we solve for the exponents and show `n = p ^ 2 * q` or `p ^ 5`, etc.
        have : (∃ p, Nat.Prime p ∧ n = p ^ 5)
              ∨ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p ^ 2 * q := by
          rcases mul_cases with ⟨hp1, hq2⟩ | ⟨hp1, hq2⟩
          · -- Case: n.factorization p + 1 = 2 and n.factorization q + 1 = 3
            have ep : n.factorization p = 1 := by simpa using hp1
            have eq_exponent : n.factorization q = 2 := by simpa using hq2
            have eq : n = p ^ 1 * q ^ 2 := by
              calc
                n = ∏ r ∈ s, r ^ n.factorization r := eq_prod_primeFactors n (by positivity)
                _ = p ^ n.factorization p * q ^ n.factorization q := by rw [hpq_ne.2, Finset.prod_pair hpq_ne.1]
                _ = p ^ 1 * q ^ 2 := by simp [ep, eq_exponent]
            exact Or.inr ⟨q, p, (mem_primeFactors.1 hq_mem).1, (mem_primeFactors.1 hp_mem).1,
                        hpq_ne.1.symm, by simp [pow_one, mul_comm] at eq ⊢; exact eq⟩
          · -- Case: n.factorization p + 1 = 3 and n.factorization q + 1 = 2
            have ep : n.factorization p = 2 := by simpa using hp1
            have eq_exponent : n.factorization q = 1 := by simpa using hq2
            have eq : n = p ^ 2 * q ^ 1 := by
              calc
                n = ∏ r ∈ s, r ^ n.factorization r := eq_prod_primeFactors n (by positivity)
                _ = p ^ n.factorization p * q ^ n.factorization q := by rw [hpq_ne.2, Finset.prod_pair hpq_ne.1]
                _ = p ^ 2 * q ^ 1 := by simp [ep, eq_exponent]
            exact Or.inr ⟨p, q, (mem_primeFactors.1 hp_mem).1, (mem_primeFactors.1 hq_mem).1,
                        hpq_ne.1, by simp [pow_one] at eq ⊢; exact eq⟩
        exact this

    · -- Conversely, assume `n = p^5` or `n = p^2 * q` with `p, q` distinct primes; show `∏ p ∈ s, n.factorization p + 1 = 6`.
      intro H
      cases H with
      | inl h =>
        obtain ⟨p, pp, rfl⟩ := h
        -- If `n = p ^ 5`, then `s = {p}` and `(p^5).factorization p = 5`.
        have hfact : (p ^ 5).factorization p = 5 := by
          rw [Nat.factorization_pow]
          simp [Prime.factorization pp]
        have hs_eq : (p ^ 5).primeFactors = {p} := by
          rw [Nat.primeFactors_prime_pow (by positivity) pp]
        calc ∏ i ∈ (p ^ 5).primeFactors, ((p ^ 5).factorization i + 1)
          = ∏ i ∈ {p}, ((p ^ 5).factorization i + 1) := by simp only [hs_eq]
          _ = (p ^ 5).factorization p + 1 := by simp
          _ = 5 + 1 := by rw [hfact]
          _ = 6 := by norm_num
      | inr h =>
        obtain ⟨p, q, pp, pq, pneqq, hn'⟩ := h
        -- If `n = p ^ 2 * q` with `p ≠ q`, then `s = {p, q}`, `n.factorization p = 2`, `n.factorization q = 1`.
        have h_pos_p : 0 < p := Prime.pos pp
        have h_pos_q : 0 < q := Prime.pos pq
        -- have h_pos_n : 0 < n := by rw [hn']; positivity

        have hpnq : ¬ p ∣ q := by
          intro h
          have : p = 1 ∨ p = q := (Nat.dvd_prime pq).mp h
          cases this with
          | inl hp1  =>
            -- p = 1 contradicts "p.Prime" (no prime equals 1)
            exact pp.ne_one hp1
          | inr hpq =>
            -- p = q contradicts the hypothesis p ≠ q
            exact pneqq hpq

        have hpc : p.Coprime q := by
            exact (Nat.Prime.coprime_iff_not_dvd pp).mpr hpnq

        have hqnp : ¬ q ∣ p ^ 2 := by
          by_contra h
          have h_dvd_p : q ∣ p := by
            rw [pow_two] at h
            exact (Nat.Prime.dvd_mul pq).mp h |>.elim id id
          have : q = 1 ∨ q = p := (Nat.dvd_prime pp).mp h_dvd_p
          cases this with
          | inl hq1 =>
            -- q = 1 contradicts "q.Prime" (no prime equals 1)
            exact pq.ne_one hq1
          | inr hqp =>
            -- q = p contradicts the hypothesis p ≠ q
            exact pneqq hqp.symm

        -- Therefore (p ^ 2) and q are coprime
        -- have hc : (p ^ 2).Coprime q := Nat.coprime_pow_left hpc 2

        have hs_eq : n.primeFactors = {p, q} := by

          calc
            _ = (p ^ 2 * q).primeFactors := by rw [hn']
            _ = (p ^ 2).primeFactors ∪ q.primeFactors := by
              -- Use `Nat.primeFactors_mul` which needs (p ^ 2)>0, q>0, and coprime (p ^ 2) q
              apply Nat.primeFactors_mul (by positivity) (by positivity)

            _ = {p} ∪ {q} := by
              -- ‣ primeFactors (p ^ 2) = {p}, since p is prime and 2 > 0
              -- ‣ primeFactors q = {q}, since q is prime
              congr
              . rw [Nat.primeFactors_prime_pow (by positivity) pp]
              . nth_rw 1 [<- Nat.pow_one q]
                rw [Nat.primeFactors_prime_pow (by positivity) pq]

            _ = {p, q} := by
              ext x
              simp [pneqq]

        have hfact_p : n.factorization p = 2 := by
          calc
            _ = (p ^ 2 * q).factorization p := by rw [hn']
            _ = (p ^ 2).factorization p + (q).factorization p := by
              have : (p ^ 2 * q).factorization = (p ^ 2).factorization + (q).factorization := Nat.factorization_mul (by positivity: p ^ 2 ≠ 0) (by positivity: q ≠ 0)
              simp [this]
            _ = 2 + 0 := by
              congr
              . have : (p ^ 2).factorization = fun₀ | p => 2 := Prime.factorization_pow (k:=2) pp
                simp [this]
              . have : (q ^ 1).factorization = fun₀ | q => 1 := Prime.factorization_pow (k:=1) pq
                exact factorization_eq_zero_of_not_dvd hpnq
            _ = 2 := by norm_num

        have hfact_q : n.factorization q = 1 := by
          calc
            _ = (p ^ 2 * q).factorization q := by rw [hn']
            _ = (p ^ 2).factorization q + (q).factorization q := by
              have : (p ^ 2 * q).factorization = (p ^ 2).factorization + (q).factorization := Nat.factorization_mul (by positivity: p ^ 2 ≠ 0) (by positivity: q ≠ 0)
              simp [this]
            _ = 0 + 1 := by
              congr
              . have : (p ^ 2).factorization = fun₀ | p => 2 := Prime.factorization_pow (k:=2) pp
                exact factorization_eq_zero_of_not_dvd hqnp
              . have : (q ^ 1).factorization = fun₀ | q => 1 := Prime.factorization_pow (k:=1) pq
                exact Prime.factorization_self pq
            _ = 1 := by norm_num

        calc ∏ i ∈ n.primeFactors, (n.factorization i + 1)
          = ∏ i ∈ {p, q}, (n.factorization i + 1) := by rw [hs_eq]
          _ = (n.factorization p + 1) * (n.factorization q + 1) := by simp [Finset.prod_pair pneqq]
          _ = (2 + 1) * (1 + 1) := by rw [hfact_p, hfact_q]
          _ = 6 := by norm_num


  simp [h1, primeFactors_prod_factorization_add_one_eq_six_iff]
