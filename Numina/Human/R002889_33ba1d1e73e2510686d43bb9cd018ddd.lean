import Mathlib

open Polynomial

/- Three real numbers have six possible orderings. -/
lemma real_le_three_cases (a b c : ℝ) :
  a ≤ b ∧ b ≤ c
  ∨ a ≤ c ∧ c ≤ b
  ∨ b ≤ a ∧ a ≤ c
  ∨ b ≤ c ∧ c ≤ a
  ∨ c ≤ a ∧ a ≤ b
  ∨ c ≤ b ∧ b ≤ a := by
    rcases le_total a b with ab_le | ba_le
    · rcases le_total b c with bc_le | cb_le
      · tauto
      · rcases le_total a c with ac_le | ca_le
        · tauto
        · tauto
    · rcases le_total b c with bc_le | cb_le
      · rcases le_total a c with ac_le | ca_le
        · tauto
        · tauto
      · tauto

/- If among three real numbers, there is one that is smaller than the other two, then there are three possible cases. -/
lemma real_partial_order_cases_three (a b c : ℝ) :
  (a ≤ b ∧ a ≤ c)
  ∨ (b ≤ c ∧ b ≤ a)
  ∨ (c ≤ a ∧ c ≤ b) := by
    rcases real_le_three_cases a b c with g1 | g1 | g1 | g1 | g1 | g1
    all_goals
    · have := g1.1.trans g1.2
      tauto

/- Negation distributes over the coefficients of quadratics -/
lemma neg_quadratic_distrib (a b c : ℝ) : -(C a * X ^ 2 + C b * X + C c) = C (-a) * X ^ 2 + C (-b) * X + C (-c) := by
  apply Polynomial.funext
  intro x
  norm_num
  ring_nf

/- Vieta's formulas for quadratic polynomials gives us relationships between the roots and coefficients -/
lemma vieta_quadratic : ∀ {a b c d e : ℝ}, (a ≠ 0) → (C a * X ^ 2 + C b * X + C c).roots = {d, e} → (c = a * (d * e) ∧ b = a * -(d + e)) := by
  intro a b c d e ah h
  -- let p be the polynomial a * x ^ 2 + b * x + c with roots d and e
  set p := (C a * X ^ 2 + C b * X + C c) with hp

  -- then p has degree 2
  have degree : p.natDegree = 2 := Polynomial.natDegree_quadratic ah

  -- and as many roots as degree
  have roots_card : p.roots.card = p.natDegree := by
    rw [degree, h]
    norm_num

  -- 0th coefficient of p is c, 1st coefficient of p is b
  have coeff_0 : p.coeff 0 = c := by unfold p; norm_num
  have coeff_1 : p.coeff 1 = b := by unfold p; norm_num

  -- p has a leading coefficient of a
  have leading : p.leadingCoeff = a := Polynomial.leadingCoeff_quadratic ah

  -- 0 and 1 are less than or equal to the degree, so it makes sense to talk about the 0th and 1st coefficient
  have zero_le : 0 ≤ p.natDegree := by linarith
  have one_le : 1 ≤ p.natDegree := by linarith

  constructor
  -- apply the general form of Vieta's formula to the 0th coefficient of p
  · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card zero_le

    -- simplifying we get c = a * (d * e)
    simpa only [coeff_0, leading, degree, tsub_zero, even_two, Even.neg_pow, one_pow, mul_one,
      Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, Nat.reduceAdd,
      Multiset.card_singleton, Nat.one_lt_ofNat, Multiset.powersetCard_eq_empty,
      Multiset.powersetCard_one, Multiset.map_singleton, zero_add, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.sum_singleton, one_mul] using vieta
  -- apply the general form of Vieta's formula to the 1st coefficient of p
  · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card one_le
    -- simplifying we get b = a * -(d + e)
    simp only [coeff_1, leading, degree, Nat.add_one_sub_one, pow_one, mul_neg, mul_one,
      Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, zero_add,
      Multiset.powersetCard_one, Multiset.map_singleton, Multiset.powersetCard_zero_left,
      Multiset.cons_zero, Multiset.singleton_add, Multiset.map_cons, Multiset.prod_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, neg_mul, one_mul, neg_add_rev] at vieta
    linarith

/- If the sum and product of two real numbers are positive, then each number is positive. -/
lemma pos_of_add_pos_of_mul_pos {a b : ℝ} (add_pos : 0 < a + b) (mul_pos : 0 < a * b) : 0 < a ∧ 0 < b := by
  rw [mul_pos_iff] at mul_pos
  rcases mul_pos with h1 | h2
  · exact h1
  · linarith

/- The cardinality of a pair, filtered by some property p, is equal to two "if then else" statements -/
lemma multiset_filter_card_pair (a b : ℝ) (p : ℝ → Prop) [DecidablePred p] : (({a, b} : Multiset ℝ).filter p).card
  = (if p a then 1 else 0) + (if p b then 1 else 0) := by
    simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton,
      Multiset.empty_eq_zero, Multiset.card_add, apply_ite Multiset.card, Multiset.card_singleton,
      Multiset.card_zero]

/- 4. Given three non-zero real numbers $a, b, c$ such that the equations: $a x^{2}+b x+c=0, b x^{2}+c x+a=0, c x^{2}+a x+b=0$ each have two roots. How many of the roots of these equations can be negative? -/
theorem algebra_126792 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (p q r : ℝ[X])
  (p_eq : p = C a * X ^ 2 + C b * X + C c)
  (q_eq : q = C b * X ^ 2 + C c * X + C a)
  (r_eq : r = C c * X ^ 2 + C a * X + C b)
  (p1 p2 q1 q2 r1 r2 : ℝ)
  (p_roots : p.roots = {p1, p2})
  (q_roots : q.roots = {q1, q2})
  (r_roots : r.roots = {r1, r2}) :
    ((p.roots + q.roots + r.roots).filter (· < 0)).card = 2
  := by

    -- wlog, a b c are all positive or one of them is negative while the other are positive
    wlog hww : (0 < a ∧ 0 < b ∧ 0 < c)
      ∨ (a < 0 ∧ 0 < b ∧ 0 < c)
      ∨ (0 < a ∧ b < 0 ∧ 0 < c)
      ∨ (0 < a ∧ 0 < b ∧ c < 0)
    · have han : -a ≠ 0 := neg_ne_zero.mpr ha
      have hbn : -b ≠ 0 := neg_ne_zero.mpr hb
      have hcn : -c ≠ 0 := neg_ne_zero.mpr hc
      simp only [not_or, not_and_or, not_lt] at hww
      -- else we can consider -a, -b, and -c
      have app := this (-a) (-b) (-c) han hbn hcn (-p) (-q) (-r) ?_ ?_ ?_ p1 p2 q1 q2 r1 r2 ?_ ?_ ?_ ?_
      · convert app using 3
        simp only [roots_neg]
      -- negation distributes over quadratics
      · exact p_eq ▸ neg_quadratic_distrib a b c
      · exact q_eq ▸ neg_quadratic_distrib b c a
      · exact r_eq ▸ neg_quadratic_distrib c a b
      -- negation preserves roots
      · exact roots_neg p ▸ p_roots
      · exact roots_neg q ▸ q_roots
      · exact roots_neg r ▸ r_roots
      -- consider sign cases of a b and c
      · rcases lt_or_gt_of_ne ha with neg_a | pos_a
        · have a_neg_pos : 0 < -a := by linarith
          have a_not_nonpos : ¬0 ≤ a := by linarith
          have a_nonneg : a ≤ 0 := by linarith
          have a_not_neg : ¬-a < 0 := by linarith
          rcases lt_or_gt_of_ne hb with neg_b | pos_b
          · have b_neg_pos : 0 < -b := by linarith
            have b_not_nonpos : ¬0 ≤ b := by linarith
            have b_nonneg : b ≤ 0 := by linarith
            rcases lt_or_gt_of_ne hc with neg_c | pos_c
            · have c_neg_pos : 0 < -c := by linarith
              simp only [a_neg_pos, b_neg_pos, c_neg_pos]
              norm_num
            · have c_neg_pos : -c < 0 := by linarith
              simp only [a_neg_pos, b_neg_pos, c_neg_pos, a_not_neg]
              norm_num
          · have b_not_neg_pos : ¬0 < -b := by linarith
            have b_nonpos : 0 ≤ b := by linarith
            have b_not_nonneg : ¬b ≤ 0 := by linarith
            rcases lt_or_gt_of_ne hc with neg_c | pos_c
            · have c_neg_pos : 0 < -c := by linarith
              simp only [a_neg_pos, b_not_neg_pos, c_neg_pos]
              norm_num
              exact pos_b
            · have c_not_nonneg : ¬c ≤ 0 := by linarith
              simp [a_nonneg, a_not_nonpos, b_not_nonneg, c_not_nonneg] at hww
        · have a_not_neg_pos : ¬0 < -a := by linarith
          have a_nonpos : 0 ≤ a := by linarith
          have a_not_nonneg : ¬a ≤ 0 := by linarith
          have a_neg : -a < 0 := by linarith
          rcases lt_or_gt_of_ne hb with neg_b | pos_b
          · have b_neg_pos : 0 < -b := by linarith
            have b_not_nonpos : ¬0 ≤ b := by linarith
            have b_nonneg : b ≤ 0 := by linarith
            rcases lt_or_gt_of_ne hc with neg_c | pos_c
            · have c_neg_pos : 0 < -c := by linarith
              simp only [a_neg, a_not_neg_pos, b_neg_pos, c_neg_pos]
              norm_num
            · have c_neg : 0 < c := by linarith
              have c_nonneg : 0 ≤ c := by linarith
              have c_not_nonpos : ¬c ≤ 0 := by linarith
              simp only [a_nonpos, a_not_nonneg, b_nonneg, b_not_nonpos, c_nonneg, c_not_nonpos] at hww
              norm_num at hww
          · have b_not_neg_pos : ¬0 < -b := by linarith
            have b_nonpos : 0 ≤ b := by linarith
            have b_not_nonneg : ¬b ≤ 0 := by linarith
            have b_neg_neg : -b < 0 := by linarith
            rcases lt_or_gt_of_ne hc with neg_c | pos_c
            · have c_nonpos : c ≤ 0 := by linarith
              have c_not_nonneg : ¬0 ≤ c := by linarith
              simp only [a_nonpos, a_not_nonneg, b_nonpos, b_not_nonneg, c_nonpos, c_not_nonneg] at hww
              norm_num at hww
            · have c_nonpos : ¬c ≤ 0 := by linarith
              have c_not_nonneg : 0 ≤ c := by linarith
              simp only [a_nonpos, a_not_nonneg, b_nonpos, b_not_nonneg, c_nonpos, c_not_nonneg] at hww
              norm_num at hww

    -- using symmetries we only have two cases
    -- 1. 0 < a ≤ b ≤ c
    -- 2. 0 < a, 0 < b and c < 0
    wlog hw : (0 < a ∧ a ≤ b ∧ a ≤ c) ∨ (0 < a ∧ 0 < b ∧ c < 0)
    · have han : -a ≠ 0 := neg_ne_zero.mpr ha
      have hbn : -b ≠ 0 := neg_ne_zero.mpr hb
      have hcn : -c ≠ 0 := neg_ne_zero.mpr hc
      rcases hww with all_pos | a_neg | b_neg | c_neg
      · rcases real_partial_order_cases_three a b c with g1 | g1 | g1
        · have app := this a b c ha hb hc p q r p_eq q_eq r_eq p1 p2 q1 q2 r1 r2 p_roots q_roots r_roots ?_ ?_
          exact app
          tauto
          exact Or.inl ⟨all_pos.1, g1⟩
        · have app := this b c a hb hc ha q r p q_eq r_eq p_eq q1 q2 r1 r2 p1 p2 q_roots r_roots p_roots ?_ ?_
          convert app using 3
          · exact add_rotate p.roots q.roots r.roots
          · tauto
          · exact Or.inl ⟨all_pos.2.1, g1⟩
        · have app := this c a b hc ha hb r p q r_eq p_eq q_eq r1 r2 p1 p2 q1 q2 r_roots p_roots q_roots ?_ ?_
          convert app using 3
          · exact (add_rotate r.roots p.roots q.roots).symm
          · tauto
          · exact Or.inl ⟨all_pos.2.2, g1⟩
      · have app := this b c a hb hc ha q r p q_eq r_eq p_eq q1 q2 r1 r2 p1 p2 q_roots r_roots p_roots ?_ ?_
        convert app using 3
        exact add_rotate p.roots q.roots r.roots
        · refine Or.inr <| Or.inr <| Or.inr ?_
          tauto
        · tauto
      · have app := this c a b hc ha hb r p q r_eq p_eq q_eq r1 r2 p1 p2 q1 q2 r_roots p_roots q_roots ?_ ?_
        convert app using 3
        exact (add_rotate _ _ _).symm
        · refine Or.inr <| Or.inr <| Or.inr ?_
          tauto
        · tauto
      · tauto
    clear hww

    -- we consider the two cases
    rcases hw with pos | one_neg
    · have a_sq_le : a ^ 2 ≤ b * c := by nlinarith
      have bc_le : b * c < 4 * (b * c) := by nlinarith

      -- then the discriminant of c * x ^ 2 + a * x + b is negative
      have disc_negative : discrim c a b < 0 := by
        unfold discrim
        linarith

      -- so it's never equal to zero
      have not_eq_zero : ∀ x, c * (x * x) + a * x + b ≠ 0 := by
        intro x
        apply (quadratic_eq_zero_iff_discrim_eq_sq hc x).mp.mt
        by_contra eq_sq
        have discrim_pos : 0 ≤ discrim c a b := by
          rw [eq_sq]
          positivity

        -- contradiction
        linarith

      -- so r has no roots
      have r_roots_empty : r.roots = ∅ := by
        rw [r_eq]
        ext x
        simp only [pow_two, count_roots, Multiset.empty_eq_zero, Multiset.not_mem_zero,
          not_false_eq_true, Multiset.count_eq_zero_of_not_mem, rootMultiplicity_eq_zero_iff,
          IsRoot.def, eval_add, eval_mul, eval_C, eval_X]
        intro xh
        exact absurd xh (not_eq_zero x)

      -- but r has two roots, contradiction
      rw [r_roots_empty] at r_roots
      norm_num at r_roots
    -- consider the case when a and b are positive, while c is negative
    · simp only [Multiset.filter_add, Multiset.card_add]
      have ⟨aa, bb, cc⟩ := one_neg

      -- p has one negative root
      have p_neg_card : (p.roots.filter (· < 0)).card = 1 := by
        -- consider vietas formulas of p
        have p_vieta := vieta_quadratic ha (p_eq ▸ p_roots)

        -- the product of p's roots are negative
        have prod_pos : a * (p1 * p2) < 0 := by linarith
        replace prod_pos : p1 * p2 < 0 := (pos_iff_neg_of_mul_neg prod_pos).mp aa


        -- then only one of the roots is negative
        rw [p_roots, multiset_filter_card_pair]

        -- split on which root is negative
        rcases mul_neg_iff.mp prod_pos with ⟨h2, h3⟩ | ⟨h4, h5⟩
        · simp only [h3, ↓reduceIte, add_left_eq_self, ite_eq_right_iff, one_ne_zero, imp_false,
            not_lt, ge_iff_le]
          exact le_of_lt h2
        · simp only [h4, ↓reduceIte, add_right_eq_self, ite_eq_right_iff, one_ne_zero, imp_false,
            not_lt, ge_iff_le]
          exact le_of_lt h5

      -- q has no negative roots
      have q_neg_card : (q.roots.filter (· < 0)).card = 0 := by
        -- consider vietas formulas of q
        have q_vieta := vieta_quadratic hb (q_eq ▸ q_roots)

        -- the product of q's roots are positive
        have prod_pos : 0 < b * (q1 * q2) := by linarith
        replace prod_pos : 0 < (q1 * q2)
          := (pos_iff_pos_of_mul_pos prod_pos).mp bb

        -- the sum of q's roots are positive
        have sum_pos : 0 < b * (q1 + q2) := by linarith
        replace sum_pos : 0 < q1 + q2 := (pos_iff_pos_of_mul_pos sum_pos).mp bb

        -- so both roots are positive
        have ⟨q1_pos, q2_pos⟩ := pos_of_add_pos_of_mul_pos sum_pos prod_pos

        -- so the sum is zero
        rw [q_roots, multiset_filter_card_pair]
        simp only [AddLeftCancelMonoid.add_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false,
          not_lt]

        exact ⟨le_of_lt q1_pos, le_of_lt q2_pos⟩

      -- r has one negative root
      have r_neg_card : (r.roots.filter (· < 0)).card = 1 := by
        -- consider vietas formulas of r
        have r_vieta := vieta_quadratic hc (r_eq ▸ r_roots)

        -- the product of r's roots are negative
        have prod_pos : 0 < c * (r1 * r2) := by linarith
        replace prod_pos : r1 * r2 < 0 := (neg_iff_neg_of_mul_pos prod_pos).mp cc

        -- then only one of the roots is negative
        rw [r_roots, multiset_filter_card_pair]

        -- split on which root is negative
        rcases mul_neg_iff.mp prod_pos with ⟨h2, h3⟩ | ⟨h4, h5⟩
        · simp only [h3, ↓reduceIte, add_left_eq_self, ite_eq_right_iff, one_ne_zero, imp_false,
            not_lt, ge_iff_le]
          exact le_of_lt h2
        · simp only [h4, ↓reduceIte, add_right_eq_self, ite_eq_right_iff, one_ne_zero, imp_false,
            not_lt, ge_iff_le]
          exact le_of_lt h5

      -- so in total, there are 2 negative roots
      rw [p_neg_card, q_neg_card, r_neg_card]