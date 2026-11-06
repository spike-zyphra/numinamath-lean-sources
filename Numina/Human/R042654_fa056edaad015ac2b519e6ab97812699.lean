import Mathlib

set_option maxRecDepth 10000

open Polynomial

/- Find the number of second-degree [polynomials](https://artofproblemsolving.com/wiki/index.php/Polynomial) $f(x)$ with integer [coefficients](https://artofproblemsolving.com/wiki/index.php/Coefficient) and integer zeros for which $f(0)=2010$. -/
theorem algebra_94578 :
    {(f : Polynomial ℤ) | ∃ x y, f.natDegree = 2 ∧ f.eval 0 = 2010 ∧ f.roots = {x, y}}.ncard = 163 := by

    -- Our strategy will be to consider `f = a * (x - r) * (x - s)`, so `a * r * s = 2010`,
    -- and counting possible values and signs of `a`, `r` and `s`.

    -- Lemma to get roots of second-degree polynomial
    have get_roots : ∀ {a r s : ℤ}, a ≠ 0 → (C a * (X - C r) * (X - C s)).roots = {r, s} := by
      intro a r s hh
      ext p
      simp only [count_roots]
      rw [Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_mul,
        Polynomial.rootMultiplicity_C, Polynomial.rootMultiplicity_X_sub_C,
        Polynomial.rootMultiplicity_X_sub_C]
      split_ifs with a1 a2 a3
      · rw [←a1, ←a2]
        simp only [zero_add, Nat.reduceAdd, Multiset.insert_eq_cons, Multiset.count_cons_self,
          Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem]
      · subst a1
        simp only [zero_add, add_zero, Multiset.insert_eq_cons, Multiset.nodup_cons,
          Multiset.mem_singleton, a2, not_false_eq_true, Multiset.nodup_singleton, and_self,
          Multiset.mem_cons, or_false, Multiset.count_eq_one_of_mem]
      · subst a3
        simp only [add_zero, zero_add, Multiset.insert_eq_cons, ne_eq, a1, not_false_eq_true,
          Multiset.count_cons_of_ne, Multiset.nodup_singleton, Multiset.mem_singleton,
          Multiset.count_eq_one_of_mem]
      simp only [add_zero, Multiset.insert_eq_cons, Multiset.mem_cons, a1, Multiset.mem_singleton,
        a3, or_self, not_false_eq_true, Multiset.count_eq_zero_of_not_mem]
      simp only [eq_intCast, ne_eq, mul_eq_zero, Int.cast_eq_zero, hh, false_or]
      exact X_sub_C_ne_zero r
      simp only [eq_intCast, ne_eq, mul_eq_zero, Int.cast_eq_zero, hh, false_or, not_or]
      exact ⟨X_sub_C_ne_zero r, X_sub_C_ne_zero s⟩

    -- We write the polynomial as product of roots
    convert_to {(f : Polynomial ℤ) | ∃ a r s : ℤ, f = C a * (X - C r) * (X - C s) ∧ f.eval 0 = 2010}.ncard = 163
    · congr
      ext p
      constructor
      -- Every degree two polynomial with two roots can be expressed as wanted
      · simp only [Set.mem_setOf_eq]
        intro ⟨r, s, deg, ev, root⟩
        -- We consider the polynomial p as a polynomial with rational coefficients, pq
        let pq : ℚ[X] := p.map (Int.castRingHom ℚ)

        -- Roots are the same as p
        have pq_roots : p.roots.map (Int.castRingHom ℚ) = roots pq := by
          unfold pq
          refine (Polynomial.roots_map_of_injective_of_card_eq_natDegree Rat.intCast_injective ?_)
          rw [root]
          simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton,
            Nat.reduceAdd]
          exact deg.symm
        -- degree is the same as p
        have degree : (map (Int.castRingHom ℚ) p).natDegree = natDegree p := by
          simp only [natDegree_map_eq_iff, eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero]
          simp only [deg, OfNat.ofNat_ne_zero, or_false]
          refine degree_ne_bot.mp ?_
          rw [(Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr deg]
          decide
        -- We can split up pq
        have split_pq : Splits (RingHom.id _) pq := by
          refine splits_iff_card_roots.mpr ?_
          simp only [←pq_roots, Multiset.card_map]
          convert degree.symm
          simpa only [root, Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton,
            Nat.reduceAdd] using deg.symm


        refine ⟨leadingCoeff p, r, s, ?_, ev⟩

        -- Our map to rational polynomials is injective, so we just need to show
        -- that our rational polynomials are equal
        refine Polynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int ?_

        -- We split up pq
        have pq_eq_splits := Polynomial.eq_prod_roots_of_splits_id split_pq
        unfold pq at pq_eq_splits
        rw [pq_eq_splits]

        -- Simplify leading coefficient
        have lead_eq : (p.map (Int.castRingHom ℚ)).leadingCoeff = (p.leadingCoeff : ℚ) := by
          rw [← coeff_natDegree, coeff_map, eq_intCast, Int.cast_inj, degree, coeff_natDegree]

        -- Simplify
        simp only [lead_eq, map_intCast, ← pq_roots, root, Multiset.insert_eq_cons, eq_intCast,
          Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
          Polynomial.map_mul, Polynomial.map_intCast, Polynomial.map_sub, map_X]

        -- We're done
        ring_nf

      -- Other direction is clearly true
      · simp only [exists_and_right, Set.mem_setOf_eq,
          exists_and_left, and_imp, forall_exists_index]
        intro a r s ph a1
        simp only [a1, true_and]

        by_cases ha : a = 0
        · rw [ha] at ph
          simp only [eq_intCast, Int.cast_zero, zero_mul] at ph
          rw [ph] at a1
          simp only [eval_zero, OfNat.zero_ne_ofNat] at a1

        constructor
        · rw [ph, natDegree_mul, natDegree_mul ?_ (X_sub_C_ne_zero r), natDegree_sub_C, natDegree_sub_C]
          simp only [eq_intCast, natDegree_intCast, natDegree_X, zero_add, Nat.reduceAdd]
          · rwa [eq_intCast, ne_eq, Int.cast_eq_zero]
          · simpa only [eq_intCast, ne_eq, mul_eq_zero, Int.cast_eq_zero, ha, false_or] using X_sub_C_ne_zero r
          · exact X_sub_C_ne_zero s
        · refine ⟨r, s, ?_⟩
          rw [ph]
          exact get_roots ha

    -- Let's consider just the triples `(a,x,y)` where `a * x * y = 2010`
    convert_to ((fun ⟨a, r, s⟩ => C a * (X - C r) * (X - C s)) '' {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010}).ncard = 163
    · congr
      ext p
      simp only [eq_intCast, exists_and_right, Set.mem_setOf_eq, Set.mem_image, Prod.exists]
      constructor
      intro ⟨⟨a, r, s, h⟩, hm⟩
      refine ⟨a, r, s, ?_, h.symm⟩
      simpa only [h, eval_mul, eval_intCast, Int.cast_id, eval_sub, eval_X, zero_sub, mul_neg, neg_mul,
        neg_neg] using hm
      intro ⟨a, r, s, h1, h2⟩
      refine ⟨⟨a, r, s, h2.symm⟩, ?_⟩
      simpa only [← h2, eval_mul, eval_intCast, Int.cast_id, eval_sub, eval_X, zero_sub, mul_neg,
        neg_mul, neg_neg] using h1

    -- Use encard to handle sums better
    convert_to ((fun ⟨a, r, s⟩ => C a * (X - C r) * (X - C s)) '' {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010}).encard.toNat = 163

    -- A non-zero product of 3 numbers means the numbers are non-zero
    have eq_2010 : ∀ {a r s : ℤ}, a * r * s = 2010 → a ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 := by
      intro a b c ha
      by_contra hmm
      simp only [not_and_or, ne_eq, Decidable.not_not] at hmm
      rcases hmm with h1 | h1 | h1
      all_goals
      · simp only [h1, mul_zero, zero_mul, OfNat.zero_ne_ofNat] at ha

    -- Split into cases where r = s and r < s (which is equivalent to s < r)
    convert_to (
      ((fun ⟨a, r, s⟩ => C a * (X - C r) * (X - C s)) '' {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r = s}).encard
      + ((fun ⟨a, r, s⟩ => C a * (X - C r) * (X - C s)) '' {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r < s}).encard).toNat = 163
    · rw [←Set.encard_union_eq]
      · rw [←Set.image_union]
        congr
        ext p
        simp only [eq_intCast, Set.mem_image, Set.mem_setOf_eq, Prod.exists, Set.mem_union]
        constructor
        · intro ⟨a, r, s, h1, h2⟩
          by_cases le : r ≤ s
          · refine ⟨a, r, s, ?_, h2⟩
            simp only [h1, true_and]
            exact Int.le_iff_eq_or_lt.mp le
          · refine ⟨a, s, r, ?_⟩
            · simp only [not_le.mp le, and_true, ←h1, ←h2]
              ring_nf
              tauto
        · tauto
      · rw [Set.disjoint_left]
        intro p
        simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, not_exists, not_and,
          and_imp, forall_exists_index]
        intro a r s ha hb hc a1 x1 y1 hb1 lt

        by_contra con
        apply_fun Polynomial.roots at hc con
        rw [get_roots (eq_2010 ha).1] at hc

        rw [get_roots (eq_2010 hb1).1, ←hc, hb] at con
        simp only [Multiset.cons_eq_cons, Multiset.insert_eq_cons, Multiset.singleton_inj, ne_eq,
          Multiset.singleton_eq_cons_iff, exists_eq_right_right, and_true] at con
        rcases con with ⟨eq1, eq2⟩ | ⟨_, eq1, eq2⟩
        · rw [eq1, eq2] at lt
          exact (lt_self_iff_false s).mp lt
        · rw [eq1, eq2] at lt
          exact (lt_self_iff_false x1).mp lt

    -- Mapping to polynomials is injective on each set...
    have poly_inj : Set.InjOn (fun ⟨a, r, s⟩ => C a * (X - C r) * (X - C s))
      ({⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r = s} ∪ {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r < s}) := by
      intro ⟨a, r, s⟩
      simp only [Set.mem_union, Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
      intro aa
      intro a' r' s' gg hh
      apply_fun roots at hh
      have hue : a * r * s = 2010 := by tauto
      have hue' : a' * r' * s' = 2010 := by tauto
      have ⟨a_ne, r_ne, s_ne⟩ := eq_2010 hue
      have ⟨a_ne', r_ne', s_ne'⟩ := eq_2010 hue'
      rw [get_roots a_ne, get_roots a_ne'] at hh
      simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_inj, and_self,
        ne_eq, Multiset.singleton_eq_cons_iff, exists_eq_right_right, and_true] at hh
      rcases hh with ⟨h1, h2⟩ | ⟨h3, h4, h5⟩
      · subst h1 h2
        simp only [← hue, mul_eq_mul_right_iff, r_ne, or_false, s_ne] at hue'
        exact ⟨hue'.symm, rfl, rfl⟩
      · omega

    -- ...so now we can focus on just the integer triples
    convert_to ({⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r = s}.encard
      + {⟨a, r, s⟩ : ℤ × ℤ × ℤ | a * r * s = 2010 ∧ r < s}.encard).toNat = 163
    · congr 2
      · exact Set.InjOn.encard_image <| Set.InjOn.mono Set.subset_union_left poly_inj
      · exact Set.InjOn.encard_image <| Set.InjOn.mono Set.subset_union_right poly_inj

    -- Split up into sign cases, so we can work with ℕ × ℕ × ℕ
    let f1 : ℕ × ℕ × ℕ → ℤ × ℤ × ℤ := (fun (a, b, c) => ( a,  b,  c))
    let f2 : ℕ × ℕ × ℕ → ℤ × ℤ × ℤ := (fun (a, b, c) => (-a,  b, -c))
    let f3 : ℕ × ℕ × ℕ → ℤ × ℤ × ℤ := (fun (a, b, c) => ( a, -b, -c))
    let f4 : ℕ × ℕ × ℕ → ℤ × ℤ × ℤ := (fun (a, b, c) => (-a, -b,  c))
    -- S is the set of triples we
    let S := {(a, x, y) : ℕ × ℕ × ℕ | a * x * y = 2010}

    -- Each sign case is injective
    have ⟨f1_inj, f2_inj, f3_inj, f4_inj⟩ : f1.Injective ∧ f2.Injective ∧ f3.Injective ∧ f4.Injective := by
      simp only [Function.Injective, Prod.mk.injEq, Nat.cast_inj, and_imp, Prod.forall,
        forall_apply_eq_imp_iff₂, forall_apply_eq_imp_iff, Prod.mk.eta, forall_eq', implies_true,
        neg_inj, and_self, f1, f2, f3, f4]



    -- We'll prove that the sign cases are disjoint on S

    -- Casting ℕ → ℤ is never negative
    have nat_cast_neg : ∀ {a : ℕ} (b : ℕ), a ≠ 0 → (a : ℤ) ≠ -(b : ℤ) := by
      intro a b ha eq
      have a_pos : (0 : ℤ) ≤ a := Int.ofNat_zero_le a
      have neg_b : -(b : ℤ) ≤ 0 := by
          simp only [Left.neg_nonpos_iff, Nat.cast_nonneg]
      rw [←eq] at neg_b
      have a_eq_zero : a = 0 := Nat.cast_eq_zero.mp <| (Int.le_antisymm a_pos neg_b).symm
      exact absurd a_eq_zero ha

    -- A member of S does not have a zero
    have S_mem_ne : ∀ {x}, x ∈ S → x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 := by
      intro x xh
      simp only [Set.mem_setOf_eq, S] at xh
      -- We already proved this for integers
      zify at xh
      have z_ne := eq_2010 xh
      simp only [ne_eq, Nat.cast_eq_zero] at z_ne
      exact z_ne

    -- f1 and f3 are disjoint on S
    have disj_f1_f3 : Disjoint (f1 '' S) (f3 '' S) := by
      refine Set.disjoint_image_image ?_
      intro a a_mem b b_mem
      simp only [ne_eq, Prod.mk.injEq, Nat.cast_inj, not_and, f1, f3]
      intro aa bb
      have ⟨ne_1, ne_2, ne_3⟩ := S_mem_ne a_mem
      exact absurd bb <| nat_cast_neg b.2.1 ne_2

    -- f1 and f4 are disjoint on S
    have disj_f1_f4 : Disjoint (f1 '' S) (f4 '' S) := by
      refine Set.disjoint_image_image ?_
      intro a a_mem b b_mem
      simp only [ne_eq, Prod.mk.injEq, Nat.cast_inj, not_and, f1, f4]
      intro aa bb
      have ⟨ne_1, ne_2, ne_3⟩ := S_mem_ne a_mem
      exact absurd bb <| nat_cast_neg b.2.1 ne_2

    -- f3 and f4 are disjoint on S
    have disj_f3_f4 : Disjoint (f3 '' S) (f4 '' S) := by
      refine Set.disjoint_image_image ?_
      intro a a_mem b b_mem
      simp only [ne_eq, Prod.mk.injEq, Nat.cast_inj, not_and, f3, f4]
      intro aa bb
      have ⟨ne_1, ne_2, ne_3⟩ := S_mem_ne a_mem
      exact absurd aa <| nat_cast_neg b.1 ne_1

    -- We can split up the triples of integers into our four sign cases
    have split_signs : {(a, x, y) : ℤ × ℤ × ℤ | a * x * y = 2010}
      = (f1 '' S) ∪ (f2 '' S) ∪ (f3 '' S) ∪ (f4 '' S)
    := by
      ext ⟨a, x, y⟩
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
      constructor
      · intro hh
        rw [←exists_or, ←exists_or, ←exists_or]
        simp only [Prod.mk.injEq, Prod.exists]

        obtain ⟨a', ha'⟩ := Int.eq_nat_or_neg a
        obtain ⟨x', hx'⟩ := Int.eq_nat_or_neg x
        obtain ⟨y', hy'⟩ := Int.eq_nat_or_neg y

        refine ⟨a', x', y', ?_⟩
        rcases ha' with ha | ha
        · rcases hx' with hx | hx
          · rcases hy' with hy | hy
            · refine Or.inl <| Or.inl <| Or.inl ?_
              simp only [ha, hx, hy, and_self, and_true]
              rw [ha, hx, hy] at hh
              norm_cast at hh
            · rw [ha, hx, hy] at hh
              have neg : (a' : ℤ) * (x') * -(y') ≤ 0 := by
                simp only [mul_neg, Left.neg_nonpos_iff]
                positivity
              linarith only [neg, hh]

          · rcases hy' with hy | hy
            · rw [ha, hx, hy] at hh
              have neg : (a' : ℤ) * (-x') * y' ≤ 0 := by
                simp only [mul_neg, neg_mul, Left.neg_nonpos_iff]
                positivity
              linarith only [neg, hh]
            · refine Or.inl <| Or.inr ?_
              simp only [ha, hx, hy, and_self, and_true]
              rw [ha, hx, hy] at hh
              norm_num at hh
              norm_cast at hh
        · rcases hx' with hx | hx
          · rcases hy' with hy | hy
            · rw [ha, hx, hy] at hh
              have neg : -(a' : ℤ) * x' * y' ≤ 0 := by
                simp only [mul_neg, neg_mul, Left.neg_nonpos_iff]
                positivity
              linarith only [neg, hh]
            · refine Or.inl <| Or.inl <| Or.inr ?_
              simp only [ha, hx, hy, and_self, and_true]
              rw [ha, hx, hy] at hh
              norm_num at hh
              norm_cast at hh
          · rcases hy' with hy | hy
            · refine Or.inr ?_
              simp only [ha, hx, hy, and_self, and_true]
              rw [ha, hx, hy] at hh
              norm_num at hh
              norm_cast at hh
            · rw [ha, hx, hy] at hh
              have neg : -(a' : ℤ) * -x' * -y' ≤ 0 := by
                simp only [mul_neg, neg_mul, neg_neg, Left.neg_nonpos_iff]
                positivity
              linarith only [neg, hh]

      · rintro (((⟨⟨a', x', y'⟩, S_mem, f_eq⟩
          | ⟨⟨a', x', y'⟩, S_mem, f_eq⟩)
          | ⟨⟨a', x', y'⟩, S_mem, f_eq⟩)
          | ⟨⟨a', x', y'⟩, S_mem, f_eq⟩)
        all_goals
        · simp only [f1, f2, f3, f4, S, Prod.mk.injEq, Set.mem_setOf_eq] at f_eq S_mem
          rw [←f_eq.1, ←f_eq.2.1, ←f_eq.2.2]
          try simp only [neg_mul, mul_neg, neg_neg]
          norm_cast

    rw [Set.setOf_and, Set.setOf_and, split_signs]

    -- f2 sign pattern forces relation between r and s
    have f2_lt : ∀ {x}, x ∈ f2 '' S → x.2.2 < x.2.1 := by
      intro ⟨a, x, y⟩ hh
      simp only [Set.mem_image, Prod.exists] at hh ⊢
      obtain ⟨a', x', y', hh1, hh2⟩ := hh
      simp only [Set.mem_setOf_eq, S] at hh1
      simp only [Prod.mk.injEq, f2] at hh2
      have yeah : x' ≠ 0 := by
        by_contra hue
        simp only [hue, mul_zero, zero_mul, OfNat.zero_ne_ofNat] at hh1
      have lt : -(y' : ℤ) < x' := by
        refine Int.lt_of_sub_neg ?_
        refine Int.neg_pos.mp ?_
        norm_num
        positivity
      rw [hh2.2.1, hh2.2.2] at lt
      exact lt

    -- relations between r and s make some sign patterns impossible
    convert_to (((f1 '' S ∪ f3 '' S) ∩ {a | a.2.1 = a.2.2}).encard
      + ((f1 '' S ∪ f3 '' S ∪ f4 '' S) ∩ {a | a.2.1 < a.2.2}).encard).toNat = 163
    · congr 3
      · ext x
        simp only [Set.mem_inter_iff, and_congr_left_iff, Set.mem_setOf_eq, Set.mem_union]
        intro eqq
        constructor
        · rintro (((h1 | h2) | h3) | h4)
          · exact Or.inl h1
          · simpa only [eqq, lt_self_iff_false] using f2_lt h2
          · exact Or.inr h3
          · simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists] at h4
            obtain ⟨a', x', y', hh1, hh2⟩ := h4
            obtain ⟨x1, x2, x3⟩ := x
            simp only [f4, Prod.mk.injEq] at hh2
            simp only [Set.mem_setOf_eq, S] at hh1
            have yeah : x' ≠ 0 := by
              by_contra hue
              simp only [hue, mul_zero, zero_mul, OfNat.zero_ne_ofNat] at hh1
            rw [←hh2.2.1, ←hh2.2.2] at eqq
            have lt : -(x' : ℤ) < y' := by
              refine Int.lt_of_sub_neg ?_
              refine Int.neg_pos.mp ?_
              norm_num
              positivity
            simp only at eqq
            simp only [eqq, lt_self_iff_false] at lt
        · tauto
      · ext x
        simp only [Set.mem_inter_iff, and_congr_left_iff, Set.mem_setOf_eq, Set.mem_union]
        intro hh
        constructor
        · rintro (((h1 | h2) | h3) | h4)
          · exact Or.inl <| Or.inl h1
          · exact absurd hh <| lt_asymm <| f2_lt h2
          · exact Or.inl <| Or.inr h3
          · exact Or.inr h4
        · rintro ((h1  | h2) | h3) <;> tauto
    rw [Set.union_inter_distrib_right]

    -- Place equality restrictions on r and s before applying sign case
    convert_to ((f1 '' (S ∩ {a | a.2.1 = a.2.2}) ∪ f3 '' (S ∩ {a | a.2.1 = a.2.2})).encard +
      ((f1 '' S ∪ f3 '' S ∪ f4 '' S) ∩ {a | a.2.1 < a.2.2}).encard).toNat = 163
    · congr
      · ext ⟨a, x, y⟩
        simp only [Set.mem_inter_iff, Set.mem_image, Prod.mk.injEq, Prod.exists, Set.mem_setOf_eq, f1]
        constructor
        · intro ⟨⟨a', x', y', hh1, hh2, hh3, hh4⟩, eq⟩
          subst eq hh2 hh3
          simp only [Nat.cast_inj] at hh4
          rw [hh4] at hh1
          refine ⟨a', x', x', ?_⟩
          simp only [hh1, and_self]
        · intro ⟨a', x', y', ⟨hh1, hh5⟩, hh2, hh3, hh4⟩
          subst hh2 hh3 hh4 hh5
          refine ⟨⟨a', x', x', ?_⟩, rfl⟩
          exact ⟨hh1, rfl, rfl, rfl⟩
      · ext ⟨a, x, y⟩
        simp only [Set.mem_inter_iff, Set.mem_image, Prod.mk.injEq, Prod.exists, Set.mem_setOf_eq,
          f3]
        constructor
        · intro ⟨⟨a', x', y', hh1, hh2, hh3, hh4⟩, eq⟩
          subst eq hh2 hh3
          simp only [neg_inj, Nat.cast_inj] at hh4
          rw [hh4] at hh1
          refine ⟨a', x', x', ?_⟩
          simp only [hh1, and_self]
        · intro ⟨a', x', y', ⟨hh1, hh5⟩, hh2, hh3, hh4⟩
          subst hh2 hh3 hh4 hh5
          refine ⟨⟨a', x', x', ?_⟩, rfl⟩
          exact ⟨hh1, rfl, rfl, rfl⟩

    -- Set are disjoint so we can count them seperately
    convert_to ((f1 '' (S ∩ {a | a.2.1 = a.2.2})).encard + (f3 '' (S ∩ {a | a.2.1 = a.2.2})).encard +
      ((f1 '' S ∪ f3 '' S ∪ f4 '' S) ∩ {a | a.2.1 < a.2.2}).encard).toNat = 163
    · congr
      apply Set.encard_union_eq
      refine Set.disjoint_of_subset ?_ ?_ disj_f1_f3
      all_goals exact Set.image_mono <| Set.inter_subset_left

    -- sign cases are injective, so we ignore them when counting
    convert_to ((S ∩ {a | a.2.1 = a.2.2}).encard + (S ∩ {a | a.2.1 = a.2.2}).encard +
      ((f1 '' S ∪ f3 '' S ∪ f4 '' S) ∩ {a | a.2.1 < a.2.2}).encard).toNat = 163
    · congr 3
      · exact f1_inj.encard_image _
      · exact f3_inj.encard_image _

    -- We do the same for r < s. f4 can be simplified because (-r) < s is always true
    rw [←two_mul, Set.union_inter_distrib_right, Set.union_inter_distrib_right]
    convert_to (2 * (S ∩ {a | a.2.1 = a.2.2}).encard +
      ( f1 '' (S ∩ {a | a.2.1 < a.2.2})
      ∪ f3 '' (S ∩ {a | a.2.2 < a.2.1})
      ∪ f4 '' S
      ).encard).toNat = 163
    · congr
      · ext ⟨a, x, y⟩
        simp only [Set.mem_inter_iff, Set.mem_image, Prod.mk.injEq, Prod.exists, Set.mem_setOf_eq, f1]
        constructor
        · intro ⟨⟨a', x', y', hh1, hh2, hh3, hh4⟩, eq⟩
          refine ⟨a', x', y', ⟨⟨hh1, ?_⟩, ⟨hh2, hh3, hh4⟩⟩⟩
          rw [←hh4, ←hh3] at eq
          exact Int.ofNat_lt.mp eq
        · intro ⟨a', x', y', ⟨hh1, hh5⟩, hh2, hh3, hh4⟩
          subst hh2 hh3 hh4
          refine ⟨⟨a', x', y', hh1, rfl, rfl, rfl⟩, ?_⟩
          simpa only [Nat.cast_lt] using hh5
      · ext ⟨a, x, y⟩
        simp only [Set.mem_inter_iff, Set.mem_image, Prod.mk.injEq, Prod.exists, Set.mem_setOf_eq,
          f3]
        constructor
        · intro ⟨⟨a', x', y', hh1, hh2, hh3, hh4⟩, eq⟩
          refine ⟨a', x', y', ⟨⟨hh1, ?_⟩, ⟨hh2, hh3, hh4⟩⟩⟩
          rw [←hh4, ←hh3] at eq
          simpa only [neg_lt_neg_iff, Nat.cast_lt] using eq
        · intro ⟨a', x', y', ⟨hh1, hh5⟩, hh2, hh3, hh4⟩
          subst hh2 hh3 hh4
          refine ⟨⟨a', x', y', hh1, rfl, rfl, rfl⟩, ?_⟩
          simpa only [neg_lt_neg_iff, Nat.cast_lt] using hh5
      · ext ⟨a, x, y⟩
        simp only [Set.mem_inter_iff, Set.mem_image, Prod.mk.injEq, Prod.exists, Set.mem_setOf_eq,
          and_iff_left_iff_imp, forall_exists_index, and_imp, f4]
        intro a' x' y' S_mem eq1 eq2 eq3
        rw [←eq2, ←eq3]
        apply Int.lt_of_sub_pos
        simp only [sub_neg_eq_add]
        simp only [Set.mem_setOf_eq, S] at S_mem
        zify at S_mem
        have ⟨a_ne, x_ne, y_ne⟩ := eq_2010 S_mem
        positivity

    -- Sets are disjoint so we can count them seperately
    convert_to (2 * (S ∩ {a | a.2.1 = a.2.2}).encard +
      ((f1 '' (S ∩ {a | a.2.1 < a.2.2}) ∪ f3 '' (S ∩ {a | a.2.2 < a.2.1})).encard + (f4 '' S).encard)).toNat = 163
    · congr
      apply Set.encard_union_eq
      refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
      · refine Set.disjoint_of_subset_left ?_ disj_f1_f4
        exact Set.image_mono <| Set.inter_subset_left
      · refine Set.disjoint_of_subset_left ?_ disj_f3_f4
        exact Set.image_mono <| Set.inter_subset_left

    -- Sets are disjoint so we can count them seperately
    convert_to (2 * (S ∩ {a | a.2.1 = a.2.2}).encard +
      (((f1 '' (S ∩ {a | a.2.1 < a.2.2})).encard + (f3 '' (S ∩ {a | a.2.2 < a.2.1})).encard) + (f4 '' S).encard)).toNat = 163
    · congr
      apply Set.encard_union_eq
      refine Set.disjoint_of_subset ?_ ?_ disj_f1_f3
      all_goals exact Set.image_mono <| Set.inter_subset_left

    -- Sign cases are injective, so we ignore them when counting
    convert_to (2 * (S ∩ {a | a.2.1 = a.2.2}).encard +
      (((S ∩ {a | a.2.1 < a.2.2}).encard + (S ∩ {a | a.2.2 < a.2.1}).encard) + S.encard)).toNat = 163
    · congr 3
      congr 1
      exact f1_inj.encard_image _
      exact f3_inj.encard_image _
      exact f4_inj.encard_image _

    -- We see that we have cases for S that include r = s, r < s and r > s.
    convert_to ((S ∩ {a | a.2.1 = a.2.2}).encard +
      ((S ∩ {a | a.2.1 = a.2.2}).encard + (S ∩ {a | a.2.1 < a.2.2}).encard + (S ∩ {a | a.2.2 < a.2.1}).encard) + S.encard).toNat = 163
    · ring_nf

    -- So we combine them into S
    convert_to ((S ∩ {a | a.2.1 = a.2.2}).encard +
      S.encard + S.encard).toNat = 163
    · congr
      rw [←Set.encard_union_eq, ←Set.encard_union_eq,
      ←Set.inter_union_distrib_left, ←Set.inter_union_distrib_left]
      · congr
        refine Set.inter_eq_left.mpr ?_
        intro a b
        simp only [Set.mem_union, Set.mem_setOf_eq]
        apply ltByCases a.2.1 a.2.2 <;> tauto
      refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
      all_goals refine Disjoint.inter_left' S <| Disjoint.inter_right' S ?_
      · simp only [Set.disjoint_left, Set.mem_setOf_eq, not_lt, Prod.forall, forall_eq', le_refl, implies_true]
      · simpa only [Set.disjoint_left, Set.mem_setOf_eq, not_lt, Prod.forall, forall_const] using fun a b => Nat.le_of_succ_le
      · simpa only [Set.disjoint_left, Set.mem_setOf_eq, not_lt, Prod.forall, forall_const] using fun a b a_1 => Nat.le_of_eq a_1.symm

    -- We consider S as a clearly finite set
    let S_fin := ((Nat.divisors 2010 ×ˢ Nat.divisors 2010 ×ˢ Nat.divisors 2010).filter (fun ⟨a, x, y⟩ => a * x * y = 2010))
    have S_eq : S = S_fin.toSet := by
      ext ⟨a, x, y⟩
      simp only [Finset.coe_filter, Finset.mem_product, Nat.mem_divisors, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, and_true, Set.mem_setOf_eq, S, S_fin]
      refine iff_and_self.mpr ?_
      intro aa
      rw [←aa]
      refine ⟨?_, ?_, ?_⟩
      · rw [mul_assoc]
        exact Nat.dvd_mul_right a (x * y)
      · convert_to x ∣ x * (a * y)
        ring_nf
        exact Nat.dvd_mul_right _ _
      · convert_to y ∣ (a * x) * y
        ring_nf
        exact Nat.dvd_mul_left _ _

    rw [S_eq]
    -- The r = s intersection is a filter
    have S_inter_eq : S_fin.toSet ∩ {a | a.2.1 = a.2.2} = (S_fin.filter (fun a => a.2.1 = a.2.2)).toSet := by
      ext aa
      simp only [Finset.toSet, ←Set.setOf_and, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_filter]
    rw [S_inter_eq]

    -- Now we know that everything is finite, so we use ℕ cardinality instead of ℕ∞
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard,
      ←Nat.cast_add, ←Nat.cast_add, ENat.toNat_coe]

    -- There is only a single value where x = y
    have eq_single : (S_fin.filter (fun ⟨_, x, y⟩ => x = y)) = ({(⟨2010, 1, 1⟩ : ℕ × ℕ × ℕ)} : Finset _) := by
      decide

    rw [eq_single]

    -- Each of the four factors of `2010 = 2 * 3 * 5 * 67`
    -- has three choices to be part of: `a`, `x` or `y`.
    have eq_assignment : S_fin.card = Fintype.card (Fin 4 → Fin 3) := by decide

    -- Then there are 3 ^ 4 = 81 choices
    have assignment_card : Fintype.card (Fin 4 → Fin 3) = 81 := by decide
    rw [eq_assignment, assignment_card]

    -- 1 + 81 + 81 = 163, so we're done
    simp only [Finset.card_singleton, Nat.reduceAdd]