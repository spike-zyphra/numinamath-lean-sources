import Mathlib

/- Find the number of ordered pairs of positive integers $(m, n)$ such that $m^2n = 20^{20}$. -/
theorem number_theory_98204 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ m ^ 2 * n = 20 ^ 20}.ncard = 231 := by
  -- Let $S$ be the set of possible pairs. To solve this counting problem we construct
  -- a series of bijections, ending in an easily-countable finite set.
  let S := {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ m ^ 2 * n = 20 ^ 20}

  -- We first note that $n$ is completely determined by $m$, and $m$ must divide $20^{10}$.
  let e1 : S ≃ {m : ℕ+ | m.1 ∣ 20 ^ 10 } :=
    { toFun := fun ⟨(m, n), hm, hn, hmn⟩ => ⟨⟨m, hm⟩, by
        have : m ^ 2 ∣ (20 ^ 10) ^ 2 := by
          simp;
          exact Dvd.intro n hmn
        rw [Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)] at this
        exact this⟩
      invFun := fun ⟨m, h⟩ => ⟨(m, 20 ^ 20 / m ^ 2), by
        rcases m with ⟨m, hm⟩
        have : m ^ 2 ∣ (20 ^ 10) ^ 2 := by
          rw [Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)]
          exact h
        and_intros
        . norm_cast
        . simp
          and_intros
          . positivity
          . exact Nat.le_of_dvd (by positivity) this
        . exact Nat.mul_div_cancel_left' this⟩
      left_inv := fun ⟨(m, n), hm, hn, hmn⟩ => by
        simp
        simp at hmn
        rw [← hmn]
        rw [Nat.mul_comm]
        rw [Nat.mul_div_cancel n (by positivity)]
      right_inv := fun ⟨m, h⟩ => by norm_cast
    }

  -- Next, we pass to integer factorizations of $m$. First we note the factorization of $20^{10}$
  have N_factorization : (20 ^ 10).factorization = Finsupp.single 2 20 + Finsupp.single 5 10 := by
    have : 20 ^ 10 = 2 ^ 20 * 5 ^ 10 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_five]

  -- Some properties about the support of the factorization of $20^{10}$
  have fact_prime_supp {f : ℕ →₀ ℕ} (f_le : f ≤ (20 ^ 10).factorization) : ∀ p ∈ f.support, Nat.Prime p := by
    intro p
    simp
    intro h
    rw [N_factorization, Finsupp.le_def] at f_le
    by_cases h1 : p = 2
    . simp [h1]
      exact Nat.prime_two
    . by_cases h2 : p = 5
      . simp [h2]
        exact Nat.prime_five
      . have := f_le p
        simp [Finsupp.add_apply] at this
        rw [Finsupp.single_eq_of_ne (show 2 ≠ p by omega), Finsupp.single_eq_of_ne (show 5 ≠ p by omega)] at this
        simp at this
        contradiction

  have fact_no_zero_supp {f : ℕ →₀ ℕ} (f_le : f ≤ (20 ^ 10).factorization) : 0 ∉ f.support := by
    simp
    rw [N_factorization, Finsupp.le_def] at f_le
    have := f_le 0
    simp at this
    exact this

  -- We use the standard bijection between positive integers and factorizations, where
  -- here the factorization of $m$ is bounded by the factorization of $20^{10}$.
  let e2 : {m : ℕ+ | m.1 ∣ 20 ^ 10 } ≃ { f : ℕ →₀ ℕ | f ≤ (20 ^ 10).factorization } :=
    { toFun := fun ⟨m, hm⟩ => ⟨(m : ℕ).factorization, by
        simp
        exact (Nat.factorization_le_iff_dvd (by positivity) (by norm_num)).mpr hm⟩
      invFun := fun ⟨f, f_le⟩ => ⟨⟨f.prod (· ^ ·), Nat.prod_pow_pos_of_zero_not_mem_support (fact_no_zero_supp f_le)⟩, by
        simp
        rw [← Nat.factorization_le_iff_dvd (Nat.pos_iff_ne_zero.mp (Nat.prod_pow_pos_of_zero_not_mem_support (fact_no_zero_supp f_le))) (by norm_num)]
        rw [Nat.prod_pow_factorization_eq_self (fact_prime_supp f_le)]
        exact f_le⟩
      left_inv := fun ⟨m, hm⟩ => by simp; norm_cast
      right_inv := fun ⟨f, f_le⟩ => by simp; exact Nat.prod_pow_factorization_eq_self (fact_prime_supp f_le)
    }

  -- Finally, the set of such factorizations is determined by the multiplicities of $2$ and $5$ alone,
  -- and these must be bounded by $20$ and $10$ respectively.
  let e3 : { f : ℕ →₀ ℕ | f ≤ (20 ^ 10).factorization } ≃ Finset.Icc 0 20 ×ˢ Finset.Icc 0 10 :=
    { toFun := fun ⟨f, f_le⟩ => ⟨(f 2, f 5), by
        simp_rw [Finset.mem_product, Finset.mem_Icc]
        rw [N_factorization] at f_le
        simp [Finsupp.le_def] at f_le
        and_intros
        any_goals simp
        . have := f_le 2
          simp at this
          exact this
        . have := f_le 5
          simp at this
          exact this⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨Finsupp.single 2 a + Finsupp.single 5 b, by
        simp at h
        rcases h with ⟨ha, hb⟩
        rw [N_factorization]
        simp
        rw [Finsupp.le_def]
        intro p
        by_cases h1 : p = 2
        . simp [h1, ha]
        . by_cases h2 : p = 5
          . simp [h2, hb]
          . simp [Finsupp.add_apply]
            rw [Finsupp.single_eq_of_ne (show 2 ≠ p by omega), Finsupp.single_eq_of_ne (show 5 ≠ p by omega)]
            simp⟩
      left_inv := fun ⟨f, f_le⟩ => by
        rw [N_factorization] at f_le
        simp [Finsupp.le_def] at f_le
        ext p
        by_cases h1 : p = 2
        . simp [h1]
        . by_cases h2 : p = 5
          . simp [h2]
          . simp [Finsupp.add_apply]
            have := f_le p
            rw [Finsupp.single_eq_of_ne (show 2 ≠ p by omega), Finsupp.single_eq_of_ne (show 5 ≠ p by omega)] at *
            simp at *
            exact (symm this)
      right_inv := fun ⟨⟨a, b⟩, _⟩ => by simp
    }

  -- Finally, we can put this all together to get compute the cardinality
  calc
    S.ncard = Nat.card S := by rw [Set.Nat.card_coe_set_eq]
    _ = Nat.card {m : ℕ+ | m.1 ∣ 20 ^ 10 } := Nat.card_congr e1
    _ = Nat.card { f : ℕ →₀ ℕ | f ≤ (20 ^ 10).factorization } := Nat.card_congr e2
    _ = Nat.card (Finset.Icc 0 20 ×ˢ Finset.Icc 0 10) := Nat.card_congr e3
    _ = Finset.card (Finset.Icc 0 20 ×ˢ Finset.Icc 0 10) := by rw [Nat.card_eq_finsetCard]
    _ = 231 := by simp