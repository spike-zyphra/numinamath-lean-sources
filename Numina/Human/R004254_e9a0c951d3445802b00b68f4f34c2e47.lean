import Mathlib

/- 3. (China Girls Mathematical Olympiad) Let $m, n$ be integers, $m>n \geqslant 2, S=\{1,2, \cdots, m\}, T=\left\{a_{1}, a_{2}, \cdots, a_{n}\right\}$ be a subset of $S$. It is known that any two numbers in $T$ cannot simultaneously divide any number in $S$. Prove that: $\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}<\frac{m+n}{m}$. -/
theorem number_theory_245581 (m n : ℕ) (hmn : m > n ∧ n ≥ 2)
    (T : Finset ℕ) (T_card : T.card = n)
    (hT : T ⊆ Finset.Icc 1 m) (hT1 : ∀ x ∈ T, ∀ y ∈ T,
    x ≠ y → ¬(∃ k ∈ Finset.Icc 1 m, x ∣ k ∧ y ∣ k)) :
    ∑ x ∈ T, (1 : ℚ) / x < (m + n) / m := by

    -- use ≤ and < instead of ≥ and >
    simp only [gt_iff_lt, ge_iff_le] at hmn

    -- let S = [1, m]
    set S := Finset.Icc 1 m

    -- let T_i(a) be the elements in S which are multiples of a
    let T_i : ℕ → Finset ℕ := fun a => (S.filter (a ∣ ·))

    -- Given a ∈ T, a is positive
    have mem_pos {a : ℕ} (ah : a ∈ T) : 0 < a := by
      have a_mem_S : a ∈ S := hT ah
      norm_num [S] at a_mem_S
      omega

    -- We can bound the sum ∑ a ∈ T, |T_i(a)| ≤ m
    have sum_dvd_card_le : ∑ a ∈ T, (T_i a).card ≤ m := by
      -- each T_i is disjoint
      have pairwise_disj : (T.toSet).PairwiseDisjoint T_i
        := by simpa [T_i, Set.PairwiseDisjoint, Set.Pairwise,
                      Function.onFun, Finset.disjoint_filter] using hT1

      -- so the sum is equal to the cardinality of the disjoint sum of the sets
      rw [←Finset.card_disjiUnion _ _ pairwise_disj]

      -- which is upper bounded by the size of S
      trans S.card
      · apply Finset.card_le_card

        -- union is a subset if all parts are subsets
        simpa only [Finset.disjiUnion_eq_biUnion, Finset.biUnion_subset]
          using fun x xh => Finset.filter_subset (x ∣ ·) S

      -- and |S| = m
      norm_num [S]

    -- taking the sum over m / a_i, treating the variables as rational
    -- numbers, we have the strict upper bound
    -- ∑ a ∈ T, (⌊m / a⌋ + 1)
    have sum_le : ∑ a ∈ T, (m : ℚ) / (a : ℚ) < ∑ a ∈ T, ((m / a : ℕ) + 1) := by
      push_cast
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.card_pos.mp (by omega)

      -- it holds termwise
      · intro a ah

        have a_pos := mem_pos ah

        rw [div_lt_iff₀ (by norm_cast)]
        norm_cast
        rw [mul_comm]
        exact Nat.lt_mul_div_succ _ a_pos

    -- Given a ∈ T, |T_i(a)| = m / a (rounding down)
    have a_dvd_card {a : ℕ} (ha : a ∈ T)
      : (T_i a).card = m / a := by

      -- consider the set as integers
      trans ((T_i a).map (Nat.castEmbedding (R := ℤ))).card
      · exact (Finset.card_map Nat.castEmbedding).symm

      -- we're considering the set of integers (0, m] which are multiples of a
      trans ((Finset.Ioc (0 : ℤ) (m : ℤ)).filter ((a : ℤ) ∣ ·)).card
      · congr
        ext x
        norm_num [T_i]
        constructor
        · rintro ⟨aa, ⟨bb, cc⟩, rfl⟩
          norm_num [S] at bb
          norm_cast
        · norm_num
          intro aa bb cc

          obtain ⟨x', xh⟩ : ∃ x' : ℕ, x = x'
            := Int.eq_ofNat_of_zero_le (by omega)
          subst xh
          exists x'
          norm_num [S]
          norm_cast at aa bb cc

      -- work over the integers
      zify

      -- a is positive
      have a_pos := mem_pos ha

      -- then we have a closed form for the cardinality of the set, which is
      -- ⌊m / a⌋ - ⌊0 / a⌋
      rw [Int.Ioc_filter_dvd_card _ _ (by omega)]

      -- simplify and recall that the variables
      -- are natural numbers and we're done
      norm_num
      norm_cast
      norm_num

    -- so the upper bound is at most m + n
    have lhs_le : (((∑ a ∈ T, ((m / a : ℕ) + 1)) : ℕ) : ℚ) ≤ m + n := by
      norm_cast
      -- split out n from sum
      norm_num [Finset.sum_add_distrib, T_card]

      -- then we've already proven the pieces for
      convert_to ∑ a ∈ T, (T_i a).card ≤ m
      · exact Finset.sum_congr rfl fun _ ah => (a_dvd_card ah).symm
      exact sum_dvd_card_le

    -- so we have ∑ a ∈ T, m / a < m + n
    have lee : ∑ a ∈ T, (m : ℚ) / a < m + n := by linarith

    -- we can extract the m from the RHS
    have rhs_eq : ∑ a ∈ T, (m : ℚ) / a = m * ∑ a ∈ T, (1 : ℚ) / a := by
      rw [Finset.mul_sum]
      field_simp
    rw [rhs_eq] at lee

    -- multiply both sides by m
    rw [lt_div_iff₀ (by norm_cast; omega)]

    -- then we have the bound
    linarith
