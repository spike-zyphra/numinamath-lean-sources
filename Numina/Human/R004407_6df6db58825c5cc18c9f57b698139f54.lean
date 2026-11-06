import Mathlib

open Polynomial

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

/- If a quadratic polynomial has two roots which are non-equal, then those are all the roots of the polynomial. -/
lemma Polynomial_roots_of_mem_of_ne {a b c r1 r2 : ℝ} (h : a ≠ 0)
  (h1 : r1 ∈ (C a * X ^ 2 + C b * X + C c).roots)
  (h2 : r2 ∈ (C a * X ^ 2 + C b * X + C c).roots)
  (h12 : r1 ≠ r2)
  : (C a * X ^ 2 + C b * X + C c).roots = {r1, r2} := by
    -- the two roots is a subset of all roots (not counting duplicates)
    have two_sub : {r1, r2} ⊆ (C a * X ^ 2 + C b * X + C c).roots := by
      simpa only [Multiset.insert_eq_cons, Multiset.cons_subset, ne_eq,
        Multiset.singleton_subset] using ⟨h1, h2⟩

    -- but the two roots are not equal, so they don't contain any duplicates
    have nodup : Multiset.Nodup {r1, r2} := by norm_num [h12]

    -- so the two roots are an actual subset of all roots
    have two_le_b : {r1, r2} ≤ (C a * X ^ 2 + C b * X + C c).roots := (Multiset.le_iff_subset nodup).mpr two_sub

    -- but a quadratic polynomial has degree 2
    have degree : (C a * X ^ 2 + C b * X + C c).natDegree = 2 := by
      apply Polynomial.natDegree_quadratic
      exact h

    -- so the number of roots is less than or equal to 2
    have roots_card : (C a * X ^ 2 + C b * X + C c).roots.card ≤ 2 := by
      convert card_roots' _
      exact degree.symm

    -- so our two roots are all the roots of the polynomial
    exact (Multiset.eq_of_le_of_card_le two_le_b roots_card).symm


/- 1. Determine all values of real parameters $p$ and $q$ for which each of the equations


$$

x(x-p)=3+q, \quad x(x+p)=3-q

$$


has two distinct real roots, and the arithmetic mean of these roots is one of the roots of the other equation. -/
theorem algebra_261956 (p q : ℝ)
  (a : ℝ → Prop) (ha : a = (fun x => x * (x - p) = 3 + q))
  (b : ℝ → Prop) (hb : b = (fun x => x * (x + p) = 3 - q))
  : (∃ (a1 a2 b1 b2 : ℝ), a1 ≠ a2 ∧ b1 ≠ b2 ∧ a a1 ∧ a a2 ∧ b b1 ∧ b b2 ∧ a ((b1 + b2) / 2) ∧ b ((a1 + a2) / 2))
  ↔ (p = 2 ∨ p = -2) ∧ q = 0 := by
    constructor
    · intro ⟨a1, a2, b1, b2, a_ne, b_ne, aa1, aa2, bb1, bb2, a_avg, b_avg⟩

      -- the first equation is equal to the polynomial x ^ 2 - p * x - (3 + p)
      let a_pol : ℝ[X] := C 1 * X ^ 2 + (C (-p)) * X + C (-(3 + q))

      replace ha : a = fun x => x ∈ a_pol.roots := by
        simp only [ha, a_pol]
        ext i
        norm_num
        constructor
        · intro eq_zero
          split_ands
          -- the polynomial is non-zero
          · apply_fun (coeff · 2)
            norm_num
          · linarith
        · intro ⟨aa, bb⟩
          linarith

      -- the second equation is equal to the polynomial x ^ 2 + p * x + p - 3
      let b_pol : ℝ[X] := C 1 * X ^ 2 + (C p) * X + C (-3 + q)

      replace hb : b = fun x => x ∈ b_pol.roots := by
        simp only [hb, b_pol]
        ext i
        norm_num
        constructor
        · intro eq_zero
          split_ands
          -- the polynomial is non-zero
          · apply_fun (coeff · 2)
            norm_num
          · linarith
        · intro ⟨aa, bb⟩
          linarith

      subst ha hb

      -- one is not zero
      have one_ne_zero : (1 : ℝ) ≠ 0 := by linarith

      -- the roots of a is a1 and a2
      have a_roots : a_pol.roots = {a1, a2} := Polynomial_roots_of_mem_of_ne one_ne_zero aa1 aa2 a_ne
      -- the roots of b is b1 and b2
      have b_roots : b_pol.roots = {b1, b2} := Polynomial_roots_of_mem_of_ne one_ne_zero bb1 bb2 b_ne

      -- we use vietas formula for the sum of roots of the two polynomials
      have ⟨_, a_vieta_add⟩ := vieta_quadratic one_ne_zero a_roots
      have ⟨_, b_vieta_add⟩ := vieta_quadratic one_ne_zero b_roots
      norm_num at a_vieta_add b_vieta_add

      -- sum of roots of first polynomial are p
      replace a_veta_add : p = a2 + a1 := by linarith
      -- sum of roots of second polynomial are p
      replace b_veta_add : -p = b2 + b1 := by linarith

      -- the arithmetic mean of the roots of the first polynomial is p / 2
      have arith_mean_a : (a1 + a2) / 2 = p / 2 := by linarith
      -- the arithmetic mean of the roots of the second polynomial is -p / 2
      have arith_mean_b : (b1 + b2) / 2 = -p / 2 := by linarith

      rw [arith_mean_a] at b_avg
      rw [arith_mean_b] at a_avg

      -- so we get (3 * p ^ 2) / 4 = 3 - q
      have three_sub_eq : (3 * p ^ 2) / 4 = 3 - q := by
        norm_num [b_pol] at b_avg
        linarith

      -- and (3 * p ^ 2) / 4 = 3 + q
      have three_add_eq : (3 * p ^ 2) / 4 = 3 + q := by
        norm_num [a_pol] at a_avg
        linarith

      -- so q is zero
      have q_eq_zero : q = 0 := by linarith

      -- but then p ^ 2 = 4, so p = ±√4
      have p_eq_cases : p = √4 ∨ p = -√4 := by
        refine mul_self_eq_mul_self_iff.mp ?_
        field_simp
        linarith

      -- and √4 = 2, so p = ±2
      have sqrt_four : √4 = 2 := by
        convert_to √(2 * 2) = 2
        · ring_nf
        refine Real.sqrt_mul_self ?_
        linarith
      rw [sqrt_four] at p_eq_cases

      -- so we know the values of p and q
      tauto

    -- now we check that the values of p and q are valid
    · rintro (⟨(rfl | rfl), rfl⟩)
      -- in one case p = 2 and q = 0
      · subst ha hb
        -- then the roots are -1 and 3, 1 and -3
        exists -1, 3, 1, -3
        -- which is valid
        norm_num
      -- and the other p = -2 and q = 0
      · subst ha hb
        -- then the roots are 1 and -3, -1 and 3
        exists 1, -3, -1, 3
        -- which is valid
        norm_num