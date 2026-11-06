import Mathlib

/- Find all monic polynomials $P(x)=x^{2023}+a_{2022}x^{2022}+\ldots+a_1x+a_0$ with real coefficients such that $a_{2022}=0$, $P(1)=1$ and all roots of $P$ are real and less than $1$. -/
theorem algebra_88255 {P : Polynomial ℝ}
    : ( P.Monic
      ∧ P.degree = 2023
      ∧ P.coeff 2022 = 0
      ∧ P.eval 1 = 1
      ∧ (∀ x ∈ P.roots, x < 1)
      ∧ P.roots.card = 2023)
    ↔ P = Polynomial.X ^ 2023 := by
    constructor
    -- we'll first show that the properties imply that P = X ^ 2023
    · intro ⟨hP, hP1, hP2, hP3, hP4, hP5⟩

      -- it's degree is 2023, a natural number
      replace hP1 : P.natDegree = 2023 := Polynomial.natDegree_eq_of_degree_eq_some hP1

      -- we can split P into factors
      have P_splits : P.Splits (RingHom.id ℝ) := by
        rw [←hP1] at hP5
        -- because it has as many roots as degrees
        exact Polynomial.splits_iff_card_roots.mpr hP5

      -- so let P = ∏ (X - r_i), where r_i is the i:th root
      have P_eq_prod := Polynomial.eq_prod_roots_of_monic_of_splits_id hP P_splits

      -- the "next coefficient", i.e. the 2022th coefficent, is 0
      have hP2' : P.nextCoeff = 0 := by
        convert hP2
        trans P.coeff (P.natDegree - 1)
        · exact Polynomial.nextCoeff_of_natDegree_pos (by omega)
        congr
        omega

      -- and the 2022th coefficient is equal to -(∑ r_i)
      have coeff_sum := Polynomial.multiset_prod_X_sub_C_nextCoeff P.roots
      rw [←P_eq_prod, hP2', zero_eq_neg] at coeff_sum

      -- let s(x) = 1 - x
      let s : ℝ → ℝ := (1 - ·)

      -- then ∏ s(r_i) = 1
      have one_sub_prod : (P.roots.map s).prod = 1 := by
        rw [P_eq_prod, Polynomial.eval_multiset_prod] at hP3
        simpa using hP3

      -- and ∑ s(r_i) = 2023
      have one_sub_sum : (P.roots.map s).sum = 2023 := by
        rw [Multiset.sum_map_sub]
        simp only [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one,
          Multiset.map_id', coeff_sum, hP5, Nat.cast_ofNat, sub_zero]

      -- consider the sums and products as being over finite sets without duplicates
      rw [Multiset.prod_eq_prod_toEnumFinset] at one_sub_prod
      rw [Multiset.sum_eq_sum_toEnumFinset] at one_sub_sum

      -- every value is non-negative
      have all_nonneg  : ∀ i ∈ (Multiset.map s P.roots).toEnumFinset, 0 ≤ i.1 := by
        rintro ⟨i1, i2⟩ ih
        norm_num at ih ⊢
        have pos : 0 < Multiset.count i1 (Multiset.map s P.roots) := by omega
        have mem : i1 ∈ (Multiset.map s P.roots) := Multiset.count_pos.mp pos
        simp only [Multiset.mem_map, ne_eq, s] at mem
        obtain ⟨a, a1, a2⟩ := mem
        rw [←a2]
        norm_num
        exact le_of_lt <| hP4 a a1

      -- and we have an equality in the AM-GM inequality
      have am_gm_eq
        : ∏ i ∈ (Multiset.map s P.roots).toEnumFinset, i.1 ^ (fun x => (1 / 2023 : ℝ)) i
        = ∑ i ∈ (Multiset.map s P.roots).toEnumFinset, (fun x => 1 / 2023) i * i.1 := by
          rw [one_div, Real.finset_prod_rpow _ _ all_nonneg, ←Finset.mul_sum, one_sub_prod, one_sub_sum]
          simp

      -- so all roots are equal to some value k
      obtain ⟨k, hk⟩ : ∃ k, ∀ x ∈ P.roots, x = k := by
        -- AM-GM gives us that every s(r_i) is equal
        have am_gm_all_eq := (Real.geom_mean_eq_arith_mean_weighted_iff'
          (Multiset.map s P.roots).toEnumFinset (fun _ => 1 / 2023) Prod.fst (by norm_num) (by norm_num [hP5])
          all_nonneg).mp am_gm_eq

        -- invert and add 1 and we have the value that every r_1 is equal to
        exists 1 - ∑ i ∈ (Multiset.map s P.roots).toEnumFinset, 1 / 2023 * i.1
        intro x xh
        have pos_count_map : 0 < (Multiset.map s P.roots).count (s x) := by
          rw [Multiset.count_pos]
          exact Multiset.mem_map_of_mem s xh

        rw [←Multiset.mem_toEnumFinset _ ⟨(s x), 0⟩] at pos_count_map

        specialize am_gm_all_eq ⟨(s x), 0⟩ pos_count_map
        simp [s] at am_gm_all_eq
        simp [s, ←am_gm_all_eq]

      -- so let the roots of P be k, k, ..., k
      have P_roots_eq : P.roots = Multiset.replicate (P.roots.card) k
        := Multiset.eq_replicate_card.mpr hk

      -- we have a non-zero amount of roots
      have roots_ne : P.roots ≠ 0 := by
        apply_fun Multiset.card
        simp [hP5]

      -- so k is 0
      obtain ⟨rfl⟩ : k = 0 := by
        -- because the sum of all roots is 0
        rw [P_roots_eq] at coeff_sum
        simpa [roots_ne] using coeff_sum

      -- so P = ∏ (X - 0) = X ^ 2023
      rw [P_roots_eq] at P_eq_prod
      simp at P_eq_prod
      rw [hP5] at P_eq_prod
      exact P_eq_prod

    -- and P = X ^ 2023 is a valid solution
    · rintro rfl
      split_ands
      -- It's monic
      · exact Polynomial.monic_X_pow 2023
      -- it's degree is 2023
      · compute_degree!

      -- the 2022th coefficient is 0
      -- P(1) = 1
      -- every root is less than 1 (because 0 < 1)
      -- and it has 2023 real roots (all 0)
      all_goals
      · simp
