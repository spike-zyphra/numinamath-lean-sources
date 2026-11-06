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

/- If x_1 and x_2 satisfy vieta's formulas for some quadratic polynomial, then x_1 and x_2 are the roots of the polynomial. -/
lemma roots_of_ne_zero_of_vieta {x1 x2 a : ℝ} (ha : a ≠ 0) (hvieta : b = -a * (x1 + x2) ∧ c = a * x1 * x2) :
      (C a * X ^ 2 + C b * X + C c).roots = {x1, x2} := by
    suffices C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) by
      have h1 : C a * (X - C x1) ≠ 0 := mul_ne_zero (by simpa) (Polynomial.X_sub_C_ne_zero _)
      have h2 : C a * (X - C x1) * (X - C x2) ≠ 0 := mul_ne_zero h1 (Polynomial.X_sub_C_ne_zero _)
      simp only [this, Polynomial.roots_mul h2, Polynomial.roots_mul h1]
      rw [Polynomial.roots_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
      simp only [zero_add, Multiset.singleton_add, Multiset.insert_eq_cons]
    simpa [hvieta.1, hvieta.2] using by ring

/- If the sum and product of two real numbers are positive, then each number is positive. -/
lemma pos_of_add_pos_of_mul_pos {a b : ℝ} (add_pos : 0 < a + b) (mul_pos : 0 < a * b) : 0 < a ∧ 0 < b := by
  rw [mul_pos_iff] at mul_pos
  rcases mul_pos with h1 | h2
  · exact h1
  · linarith

/- 4. Let $k$ be one of the quotients of the roots of the quadratic equation $\left.p x^{2}-q x\right\lrcorner q=0$, where $p, q>0$. Express the roots of the equation $\sqrt{p} x^{2}-\sqrt{q} x+\sqrt{p}=0$ in terms of $k$ (not in terms of $p$ and $q$). -/
theorem algebra_216806 {p q x1 x2 k: ℝ} (hp : 0 < p) (hq : 0 < q)
    (hroots : (C p * X ^ 2 + C (-q) * X + C q).roots = {x1, x2})
    (hk : k = x1 / x2) :
    (C √p * X ^ 2 + C (-√q) * X + C √p).roots = {√k, 1 / √k} := by

    -- p is not zero
    have p_ne_zero : p ≠ 0 := by linarith

    -- use vieta's formula for p * x ^ 2 - q * x + q
    have ⟨vieta_mul, vieta_add⟩ := vieta_quadratic p_ne_zero hroots

    -- so we have q / p = x_1 + x_2
    replace vieta_add : q / p = (x1 + x2) := by
      field_simp
      linarith

    -- and q / p = x_1 * x_2
    replace vieta_mul : q / p = (x1 * x2) := by
      field_simp
      linarith

    -- q / p is positive
    have div_pos : 0 < q / p := by positivity

    -- so x_1 * x_2  is positive
    have mul_pos : 0 < x1 * x2 := by linarith
    -- and x_1 + x_2  is positive
    have add_pos : 0 < x1 + x2 := by linarith

    -- so x_1 and x_2 are both positive
    have ⟨x1_pos, x2_pos⟩ := pos_of_add_pos_of_mul_pos add_pos mul_pos

    -- we square both sides of q / p = x_1 * x_2
    have sqrt_mul : √(q / p) = √(x1 * x2) := congrArg Real.sqrt vieta_mul

    -- then we divide both sides of q / p = x_1 + x_2 by √(q / p) = √(x1 * x2)
    -- to get (x1 + x2) / √(x1 * x2) = (q / p) / √(q / p)
    have divided : (x1 + x2) / √(x1 * x2) = (q / p) / √(q / p) := by
        apply_fun (· / √(x1 * x2)) at vieta_add
        nth_rw 1 [←sqrt_mul] at vieta_add
        tauto

    -- the RHS is equal to √(q / p)
    have right_eq : (q / p) / √(q / p) = √(q / p) := Real.div_sqrt

    -- the LHS is equal to √(x1 / x2) + √(x2 / x1)
    have left_eq : (x1 + x2) / √(x1 * x2) = √(x1 / x2) + √(x2 / x1) := by
      field_simp
      ring_nf
      norm_num

    rw [right_eq, left_eq] at divided

    -- we have that 1 / k = x_2 / x_1
    have hk_2 : 1 / k = x2 / x1 := by
      rw [hk]
      field_simp

    -- then we have that √k + √(1 / k) = √(q / p)
    replace divided : √k + √(1 / k) = √(q / p) := by simpa only [←hk, ←hk_2] using divided

    -- then we can use vieta's formula in reverse to show that √k and √(1 / k) are the roots
    apply roots_of_ne_zero_of_vieta
    -- leading coefficient √p is not zero
    · positivity
    -- both vieta's formulas apply
    · split_ands
      -- in one case we use that √k + √(1 / k) = √(q / p)
      · field_simp
        rw [Real.sqrt_div (le_of_lt hq)] at divided
        field_simp at divided
        linarith
      -- the other is obviously true
      · have sqrt_p_pos : 0 < √p := by positivity
        have sqrt_k_ne_zero : √k ≠ 0 := by
          rw [hk]
          positivity
        field_simp