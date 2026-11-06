import Mathlib

/- 4. Let a function $f: \mathbb{N} \rightarrow \mathbb{N}_{0}$ be defined as follows:
1) $f(1)=0$,
2) $f(p)=1$, for every prime number $p$,
3) $f(a b)=a f(b)+b f(a)$, for all $a, b \in \mathbb{N}$.

Determine all numbers $n \in \mathbb{N}$ such that $f(n)=n$. -/
theorem number_theory_225220 (f : ℕ+ → ℕ)
    (h₀ : f 1 = 0)
    (h₁ : ∀ p, Nat.Prime p.1 → f p = 1)
    (h₂ : ∀ a b, f (a * b) = a * f b + b * f a) :
    {n | f n = n} = {n | ∃ p, Nat.Prime p ∧ n.1 = p ^ p}
  := by

    -- We extend f to zero, so we have f' : ℕ → ℕ
    let f' : ℕ → ℕ := fun x => if h : 0 < x then f ⟨x, h⟩ else 0

    -- translate properties of f to f'
    have h0 : f' 1 = 0 := by
      unfold f'
      simp only [zero_lt_one, ↓reduceDIte, PNat.mk_ofNat]
      exact h₀
    have h1 : ∀ p, Nat.Prime p → f' p = 1 := by
      intro n pn
      unfold f'
      by_cases hn : 0 < n
      · simp only [hn, ↓reduceDIte]
        apply h₁
        exact pn
      · simp only [not_lt, nonpos_iff_eq_zero] at hn
        rw [hn] at pn
        exact absurd pn Nat.not_prime_zero
    have h2 : ∀ a b, f' (a * b) = a * f' b + b * f' a := by
      intro a b
      unfold f'
      by_cases ha : 0 < a
      by_cases hb : 0 < b
      · simp only [ha, mul_pos_iff_of_pos_left, hb, ↓reduceDIte]
        convert h₂ _ _ <;> rfl
      · simp only [not_lt, nonpos_iff_eq_zero] at hb
        simp only [hb, mul_zero, lt_self_iff_false, ↓reduceDIte, ha, zero_mul, add_zero]
      · simp only [not_lt, nonpos_iff_eq_zero] at ha
        simp only [ha, zero_mul, lt_self_iff_false, ↓reduceDIte, mul_dite, mul_zero, dite_eq_ite,
          ite_self, add_zero]

    -- we have f 0 = 0
    have f_zero : f' 0 = 0 := by simpa only [mul_zero, zero_mul, add_zero] using h2 0 0

    -- The value of f' (a_1 * a_2 * ... * a_n) can be expressed as a sum where each term contains f' (a_k)
    -- like a multivalued version of f' (a * b) = a * f' b + b * f' a
    have f_eq : ∀ A : Multiset ℕ, f' A.prod = (A.map fun a_k => (A.prod / a_k) * f' a_k).sum := by
      intro A
      -- we prove it by induction on n, the size of {a_1, a_2, .., a_n}
      induction' A using Multiset.induction_on with aa bb cc
      -- true when it's empty
      · simp only [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero]
        exact h₀
      -- Given that's its true for n = k, let's prove it when n = k + 1
      · simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
        rw [h2]
        -- If the new value is zero, the whole product will be zero
        by_cases haa : aa = 0
          -- so both sides can be simplified
        · simp only [haa, zero_mul, zero_add, Nat.div_zero, Nat.zero_div, Multiset.map_const',
          Multiset.sum_replicate, smul_eq_mul, mul_zero, add_zero, mul_eq_zero,
          Multiset.prod_eq_zero_iff]
          -- and f' 0 = 0, so it's true
          exact Or.inr f_zero

        · rw [add_comm, cc]
          -- compare terms
          congr 1
          -- cancel aa
          · rw [←Nat.eq_div_of_mul_eq_right haa rfl]
          -- multiplication distributes over sum
          · rw [←smul_eq_mul, Multiset.smul_sum]
            -- simplify
            simp only [smul_eq_mul, Multiset.map_map, Function.comp_apply]
            -- sums are equal if terms are equal
            congr 1
            apply Multiset.map_congr rfl
            intro dd ee
            rw [←mul_assoc]
            congr
            refine (Nat.mul_div_assoc aa ?_).symm
            exact Multiset.dvd_prod ee

    -- when p is a prime, f' (p ^ n) = n * (p ^ (n - 1))
    have f_prime_pow : ∀ p n, Nat.Prime p → f' (p ^ n) = n * (p ^ (n - 1)) := by
      intro p n ph
      -- split up f' into into identical terms
      rw [←Multiset.prod_replicate, f_eq]
      simp only [Multiset.prod_replicate, Multiset.map_replicate, Multiset.sum_replicate,
        smul_eq_mul, mul_eq_mul_left_iff]
      by_cases hn : n = 0
      · exact Or.inr hn
      · refine Or.inl ?_
        -- f' p = 1 when p is a prime
        simp only [h1 p ph, mul_one]
        -- p ^ n / p = p ^ (n - 1), when 1 ≤ p, n
        refine Nat.div_eq_of_eq_mul_right ?_ ?_
        exact Nat.Prime.pos ph
        exact (mul_pow_sub_one hn p).symm

    -- f' n can be written as a non-recursive sum over the primefactors of n
    have f_eq_factors : ∀ n, f' n = ∑ p_i ∈ n.primeFactors, n * (n.factorization p_i) / p_i := by
      intro n
      by_cases hn : n = 0
      -- if n is zero, then f' 0 = 0 applies
      · rw [hn]
        simp only [Nat.primeFactors_zero, Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply,
          Nat.zero_div, Finset.sum_const_zero, mul_zero]
        exact f_zero

      -- rewrite n as a product of it's prime factors n = p_1 ^ b_1 * ... * p_k ^ b_k
      · nth_rw 1 [←Nat.factorization_prod_pow_eq_self hn]
        rw [Nat.prod_factorization_eq_prod_primeFactors, Finset.prod_eq_multiset_prod]
        -- split up f' (p_1 ^ b_1 * ... * p_k ^ b_k) into sum
        rw [f_eq]

        -- simplify sum
        simp only [←Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_apply,
          Finset.sum_map_val, ←Nat.prod_factorization_eq_prod_primeFactors,
          Nat.factorization_prod_pow_eq_self hn]

        -- the sums are equal because each term is equal
        refine Finset.sum_congr rfl ?_
        simp only [Nat.mem_primeFactors, ne_eq, and_imp]
        intro p ph cc dd
        -- f' (p ^ n) can be simplified when p is prime
        rw [f_prime_pow p (n.factorization p) ph]

        -- then it's just reordering divisons and multiplications
        convert_to n / p ^ n.factorization p * (n.factorization p * (p ^ (n.factorization p) / (p ^ 1))) = n * n.factorization p / p
        · congr
          rw [Nat.pow_div]
          exact (Nat.Prime.dvd_iff_one_le_factorization ph hn).mp cc
          exact Nat.Prime.pos ph
        simp only [pow_one]
        convert_to n / p ^ n.factorization p * (n.factorization p * p ^ n.factorization p / p) = n * n.factorization p / p
        · congr
          refine Eq.symm (Nat.mul_div_assoc (n.factorization p) ?_)
          exact Nat.dvd_ordProj_of_dvd hn ph cc
        rw [Nat.div_mul_div_comm]
        convert_to (n * n.factorization p) * p ^ n.factorization p / (p * p ^ n.factorization p) = n * n.factorization p / p
        congr 1
        · ring
        · ring
        -- cancel p ^ n.factorization p
        · refine Nat.mul_div_mul_right (n * n.factorization p) p ?_
          -- 0 < p ^ n.factorization p
          exact Nat.ordProj_pos n p
        -- p ^ n.factorization p ∣ n
        · exact Nat.ordProj_dvd n p
        -- p ∣ n.factorization p * p ^ n.factorization p
        · refine (Nat.Prime.dvd_mul ph).mpr ?_
          -- because p ∣ p ^ n.factorization p
          refine Or.inr ?_
          exact Nat.dvd_ordProj_of_dvd hn ph cc

    -- We'll prove both sets are equal. Consider some value n, then it's part of one set iff it's part of the other
    ext ⟨n, nh⟩
    simp only [Set.mem_setOf_eq, PNat.mk_coe]

    -- rewrite using f'
    convert_to f' n = n ↔ ∃ p, Nat.Prime p ∧ n = p ^ p
    · simp only [f', nh, ↓reduceDIte]

    -- n ≠ 0
    have hnn : n ≠ 0 := Nat.not_eq_zero_of_lt nh

    constructor
    -- let's say that f' n = n
    · intro aa
      -- we can rewrite f' as sum over factors
      rw [f_eq_factors] at aa
      -- consider the equation as real numbers (easier to handle division)
      rify at aa
      apply_fun (fun xx => xx * (n : ℝ)⁻¹) at aa
      rw [Finset.sum_mul] at aa

      -- n * n⁻¹ = 1
      have mul_inv : ↑n * (↑n : ℝ)⁻¹ = 1 := by
        refine CommGroupWithZero.mul_inv_cancel (n : ℝ) ?_
        exact Nat.cast_ne_zero.mpr hnn

      -- Simplify sum further to get ∑ x ∈ n.primeFactors, (n.factorization x) / x) = 1
      convert_to ∑ x ∈ n.primeFactors, ↑((n * n.factorization x : ℝ) / (x : ℝ)) * (↑n : ℝ)⁻¹ = 1 at aa
      · apply Finset.sum_congr rfl
        intro aa bb
        congr
        norm_cast
        refine Nat.cast_div ?_ ?_
        have hmm : aa ∣ n := by exact Nat.dvd_of_mem_primeFactors bb
        exact Dvd.dvd.mul_right hmm (n.factorization aa)
        simp only [ne_eq, Nat.cast_eq_zero]
        simp only [Nat.mem_primeFactors, ne_eq] at bb
        exact Nat.Prime.ne_zero bb.1
      convert_to ∑ x ∈ n.primeFactors, (n.factorization x) / (x : ℝ) = 1 at aa
      · apply Finset.sum_congr rfl
        intro aa bb
        rw [mul_comm, mul_div, ←mul_assoc]
        nth_rw 2 [mul_comm]
        rw [mul_inv, one_mul]

      -- Consider when n has less than 2 prime factors
      by_cases hcard : n.primeFactors.card < 2
      · interval_cases hue : n.primeFactors.card
        -- if it has 0 prime factors, then n = 1. But then we have a contradiction
        · simp only [Finset.card_eq_zero, Nat.primeFactors_eq_empty, hnn, false_or] at hue
          simp only [hue, Nat.primeFactors_one, Nat.factorization_one, Finsupp.coe_zero,
            Pi.zero_apply, CharP.cast_eq_zero, zero_div, Finset.sum_const_zero, zero_ne_one] at aa
        -- if it has 1 prime factor, then n is a power of a prime
        -- let xx be that prime
        · obtain ⟨xx, hxx⟩ := Finset.card_eq_one.mp hue
          -- xx is a prime factor of n
          have mem_xx : xx ∈ n.primeFactors := hxx ▸ Finset.mem_singleton.mpr rfl

          -- xx is a prime
          have xx_prime := Nat.prime_of_mem_primeFactors mem_xx

          -- we have that (n.factorization xx) = xx
          simp only [hxx, Finset.sum_singleton] at aa
          have div_eq : (n.factorization xx) = (xx : ℝ) := by
            refine (div_eq_one_iff_eq ?_).mp aa
            by_contra hhx
            rw [hhx] at aa
            simp only [div_zero, zero_ne_one] at aa
          simp only [Nat.cast_inj] at div_eq

          -- let us now prove that n = xx ^ xx
          refine ⟨xx, xx_prime, ?_⟩

          -- we'll show that a list of their primefactors are permuations of eachother
          apply Nat.eq_of_perm_primeFactorsList hnn
          · simp only [ne_eq, pow_eq_zero_iff', and_not_self, not_false_eq_true]

          -- prime factors of xx ^ xx are just xx * {xx}
          rw [Nat.Prime.primeFactorsList_pow]

          -- the prime factors of n are k * {xx}, for some k
          simp only [Nat.primeFactors, List.toFinset, Multiset.toFinset_eq_singleton_iff,
            Multiset.coe_card, ne_eq, List.length_eq_zero, Nat.primeFactorsList_eq_nil,
            not_or, Multiset.nsmul_singleton] at hxx
          replace ⟨⟨ww, ww2⟩, hxx⟩ := hxx
          simp only [Multiset.replicate, Multiset.coe_eq_coe, List.perm_replicate] at hxx

          -- We just need to show that k = xx
          rw [hxx]
          simp only [List.perm_replicate, List.replicate_inj, List.length_eq_zero,
            Nat.primeFactorsList_eq_nil, or_true, and_true]
          -- n.factorization xx = xx → k = xx
          rw [←Nat.primeFactorsList_count_eq, hxx] at div_eq
          simp only [List.count_replicate_self] at div_eq
          exact div_eq
          exact xx_prime
      -- Consider when n has at least 2 prime factors
      · rw [not_lt] at hcard
        -- let a ≠ b be two prime factors of n
        obtain ⟨a, b, ha, hb, ab⟩ := Finset.one_lt_card_iff.mp hcard

        -- split out a term from sum
        have subs : {a} ⊆ n.primeFactors := Finset.singleton_subset_iff.mpr ha
        rw [←Finset.sum_sdiff subs] at aa
        simp only [Finset.sum_singleton] at aa

        -- prime factors are not zero
        have mem_n_factors : ∀ x : ℕ, x ∈ n.primeFactors → x ≠ 0
          := fun x xh => Nat.Prime.ne_zero <| Nat.prime_of_mem_primeFactors xh

        -- a does not divide n.factorization a
        have a_dvd : ¬a ∣ n.factorization a := by
          -- assume opposite
          by_contra hd
          -- then a-term is at least 1
          have div_eq_one : 1 ≤ ((n.factorization a) : ℝ) / (a : ℝ) := by
            have lee : (a : ℝ) ≤ n.factorization a := by
              norm_cast
              refine Nat.le_of_dvd ?_ hd
              refine Nat.Prime.factorization_pos_of_dvd ?_ hnn ?_
              exact Nat.prime_of_mem_primeFactors ha
              exact Nat.dvd_of_mem_primeFactors ha

            refine (one_le_div₀ ?_).mpr lee
            exact Nat.cast_pos.mpr <| Nat.zero_lt_of_ne_zero (mem_n_factors a ha)

          -- then sum is less than or equal to 0
          have sum_le : ∑ x ∈ n.primeFactors \ {a}, ((n.factorization x) : ℝ) / (x : ℝ) ≤ 0 := by
            linarith only [aa, div_eq_one]

          -- but every term is at least 0
          have terms_nonneg : ∀ i ∈ n.primeFactors \ {a}, 0 ≤ ((n.factorization i) : ℝ) / (i : ℝ) := by
            intro i ih
            apply div_nonneg
            exact Nat.cast_nonneg' (n.factorization i)
            exact Nat.cast_nonneg' i

          -- so the sum is equal to zero
          have sum_eq_zero : ∑ x ∈ n.primeFactors \ {a}, ((n.factorization x) : ℝ) / (x : ℝ) = 0
            := le_antisymm sum_le <| Finset.sum_nonneg terms_nonneg

          -- so every term is zero
          have term_all_zero := (Finset.sum_eq_zero_iff_of_nonneg terms_nonneg).mp sum_eq_zero

          -- consider b
          have b_mem : b ∈ n.primeFactors \ {a} := by
            simpa only [Finset.mem_sdiff, ne_eq, Finset.mem_singleton] using ⟨hb, ab.symm⟩

          -- then the b term is zero, contradiction
          have eq_zero := term_all_zero b b_mem
          simp only [div_eq_zero_iff, Nat.cast_eq_zero] at eq_zero
          cases' eq_zero with h1 h2
          · refine absurd h1 ?_
            simp only [Nat.factorization_eq_zero_iff, not_or, Decidable.not_not]
            refine ⟨?_, ?_, hnn⟩
            exact Nat.prime_of_mem_primeFactors hb
            exact Nat.dvd_of_mem_primeFactors hb
          · exact absurd h2 <| mem_n_factors b hb

        -- isolate a term on LHS
        replace aa : (n.factorization a : ℝ) / (a : ℝ) = 1 - ∑ x ∈ n.primeFactors \ {a}, ((n.factorization x) : ℝ) / (x : ℝ) := by
          linarith only [aa]

        -- a is prime
        have a_prime : Nat.Prime a := Nat.prime_of_mem_primeFactors ha
        have a_prime' : Prime a := Nat.prime_iff.mp a_prime

        -- the product of primefactors, excluding a, is non-zero
        have ne_zero : ∏ x ∈ n.primeFactors \ {a}, (x : ℝ) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro aa aah
          exact Nat.cast_ne_zero.mpr <| mem_n_factors aa (Finset.mem_sdiff.mp aah).1

        -- we can express the sum over primefactors as N / (∏ n.primeFactors \ {a}), where N is a natural number
        obtain ⟨f, simp_sum⟩ : ∃ f : ℕ → ℕ, ∑ x ∈ n.primeFactors \ {a}, ((n.factorization x) : ℝ) / (x : ℝ)
          = ∑ x ∈ n.primeFactors \ {a}, (f x : ℝ) / (∏ x ∈ n.primeFactors \ {a}, x : ℝ) := by
            refine ⟨?_, ?_⟩
            intro x
            exact (n.factorization x) * ((∏ k ∈ n.primeFactors \ {a}, k) / x)
            refine Finset.sum_congr rfl ?_
            intro x xh
            simp only
            push_cast
            have eqq : ((((∏ k ∈ n.primeFactors \ {a}, k) / x) : ℕ) : ℝ) = ((((∏ k ∈ n.primeFactors \ {a}, k) : ℕ) : ℝ) / (x : ℝ)) := by
              refine Nat.cast_div ?_ ?_
              exact Finset.dvd_prod_of_mem id xh
              exact Nat.cast_ne_zero.mpr <| mem_n_factors x (Finset.mem_sdiff.mp xh).1
            rw [eqq]
            ring_nf
            convert_to (n.factorization x : ℝ) * (x : ℝ)⁻¹ =
              (n.factorization x : ℝ) * (x : ℝ)⁻¹ * ((((∏ k ∈ n.primeFactors \ {a}, k) : ℕ) : ℝ) * (((∏ x ∈ n.primeFactors \ {a}, ↑x) : ℕ) : ℝ)⁻¹)
            · push_cast
              ring

            have prod_ne_zero : (((∏ k ∈ n.primeFactors \ {a}, k) : ℕ) : ℝ) ≠ 0 := by
              push_cast
              exact ne_zero
            rw [(mul_inv_eq_one₀ prod_ne_zero).mpr rfl, mul_one]

        -- rewrite equation to get equality of natural numbers
        rw [simp_sum, ←Finset.sum_div, ((div_eq_one_iff_eq ne_zero).mpr rfl).symm,
          div_sub_div_same, div_eq_div_iff] at aa
        norm_cast at aa
        have prod_cast : ∏ x ∈ n.primeFactors \ {a}, (x : ℝ) = (((∏ x ∈ n.primeFactors \ {a}, x) : ℕ) : ℝ) := by
          push_cast
          exact rfl
        rw [prod_cast] at aa

        -- prove subtraction is nonnegative to push casts
        have sum_f_le_prod : ∑ x ∈ n.primeFactors \ {a}, f x ≤ ∏ k ∈ n.primeFactors \ {a}, k := by
          by_contra lt
          rw [not_le] at lt
          have sub_neg : ((((∏ k ∈ n.primeFactors \ {a}, k) : ℕ) : ℝ) - (((∑ x ∈ n.primeFactors \ {a}, f x) : ℕ) : ℝ)) < 0 := by
            rw [sub_neg]
            norm_cast

          have eq_signs_false : ∀ {a b : ℝ}, a = b → 0 ≤ a → b < 0 → False := by
            intro a b eq ha hb
            rw [eq] at ha
            linarith only [ha, hb]
          apply eq_signs_false aa
          norm_cast
          exact Nat.zero_le _
          have hmm : 0 < (a : ℝ) := by
            simp only [Nat.cast_pos]
            exact Nat.Prime.pos a_prime
          exact mul_neg_of_neg_of_pos sub_neg hmm

        rw [←Nat.cast_sub sum_f_le_prod] at aa
        norm_cast at aa

        -- a does not divide the LHS
        have a_not_dvd : ¬a ∣ n.factorization a * ∏ k ∈ n.primeFactors \ {a}, k := by
          simp only [Prime.dvd_mul a_prime', a_dvd, false_or]
          apply Prime.not_dvd_finset_prod a_prime'
          simp only [Finset.mem_sdiff, Nat.mem_primeFactors, ne_eq, Finset.mem_singleton, and_imp]
          intro aa bb cc dd ee
          have aa_prime' : Prime aa := Nat.prime_iff.mp bb
          refine (Nat.Prime.coprime_iff_not_dvd a_prime).mp ?_
          exact (Nat.coprime_primes a_prime bb).mpr fun a_1 => ee (a_1.symm)

        -- but a does divide the LHS
        have a_dvd : a ∣ n.factorization a * ∏ k ∈ n.primeFactors \ {a}, k := by
          -- because it divides the RHS
          rw [aa]
          simp only [Prime.dvd_mul a_prime']
          refine Or.inr ?_
          exact Nat.dvd_refl a

        -- contradiction
        exact False.elim (a_not_dvd a_dvd)
        · simp only [Nat.cast_ne_zero]
          exact mem_n_factors a ha
        · exact ne_zero

    -- if p is a prime, then f' (p ^ p) = p ^ p
    · intro ⟨p, ph, n_eq⟩
      rw [n_eq, f_prime_pow p p ph, ←Nat.pow_succ']
      congr
      exact Nat.succ_pred_prime ph