import Mathlib

open Polynomial

/- 3. If the equations $x^{2}+p x+q=0$ and $x^{2}+p x-q=0$ have integer solutions, then there exist integers $a$ and $b$, such that $p^{2}=a^{2}+b^{2}$. Prove! -/
theorem algebra_219645 {p q : ℝ}
    (h1 : ∃ x, x ^ 2 + p * x + q = 0) (h2 : ∀ x : ℝ, x ^ 2 + p * x + q = 0 → ∃ z : ℤ, x = z)
    (h3 : ∃ x, x ^ 2 + p * x - q = 0) (h4 : ∀ x : ℝ, x ^ 2 + p * x - q = 0 → ∃ z : ℤ, x = z)
    :
    ∃ a b : ℤ, p^2 = a^2 + b^2
  := by
    -- let D1 be the square root of the discriminant of the first polynomial
    let D1 := Real.sqrt (discrim 1 p q)

    -- ... and D2 be the square root of the discriminant of the second polynomial
    let D2 := Real.sqrt (discrim 1 p (-q))


    -- we will prove that p, q, D1, D2 are integers

    -- 1 is not equal to 0 in the reals
    have one_ne_zero : (1 : ℝ) ≠ 0 := by norm_num

    -- disriminants are positive
    have D1_pos : 0 ≤ discrim 1 p q := by
      obtain ⟨x, p1⟩ := h1
      convert_to 1 * (x * x) + p * x + q = 0 at p1
      · ring

      have as_square := (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero x).mp p1
      rw [as_square]
      positivity

    have D2_pos : 0 ≤ discrim 1 p (-q) := by
      obtain ⟨x, p2⟩ := h3
      convert_to 1 * (x * x) + p * x + (-q) = 0 at p2
      · ring

      have as_square := (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero x).mp p2
      rw [as_square]
      positivity

    -- discriminant of first polynomial is D1 squared
    have D1_mul : discrim 1 p q = D1 * D1 := (Real.mul_self_sqrt D1_pos).symm
    -- discriminant of second polynomial is D2 squared
    have D2_mul : discrim 1 p (-q) = D2 * D2 := (Real.mul_self_sqrt D2_pos).symm

    -- rewrite polynomials in standard form
    convert_to (∀ x : ℝ, 1 * (x * x) + p * x + q = 0 → ∃ z : ℤ, x = z) at h2
    · rw [one_mul, pow_two]

    convert_to (∀ x : ℝ, 1 * (x * x) + p * x + (-q) = 0 → ∃ z : ℤ, x = z) at h4
    · rw [one_mul, pow_two, ←sub_eq_add_neg]

    -- let x1 and x2 be the roots of the first equation
    obtain ⟨x1, x2, x1h, x2h⟩ : ∃ x1 x2 : ℤ, x1 = (-p + D1) / 2 ∧ x2 = (-p - D1) / 2 := by
      have as_root1 := (quadratic_eq_zero_iff one_ne_zero D1_mul ((-p + D1) / 2)).mpr (Or.inl ?_)
      obtain ⟨x1, x1h⟩ := h2 _ as_root1
      have as_root2 := (quadratic_eq_zero_iff one_ne_zero D1_mul ((-p - D1) / 2)).mpr (Or.inr ?_)
      obtain ⟨x2, x2h⟩ := h2 _ as_root2

      exact ⟨x1, x2, x1h.symm, x2h.symm⟩
      · ring
      · ring

    -- let x3 and x4 be the roots of the second equation
    obtain ⟨x3, x4, x3h, x4h⟩ : ∃ x3 x4 : ℤ, x3 = (-p + D2) / 2 ∧ x4 = (-p - D2) / 2 := by
      have as_root3 := (quadratic_eq_zero_iff one_ne_zero D2_mul ((-p + D2) / 2)).mpr (Or.inl ?_)
      obtain ⟨x3, x3h⟩ := h4 _ as_root3
      have as_root4 := (quadratic_eq_zero_iff one_ne_zero D2_mul ((-p - D2) / 2)).mpr (Or.inr ?_)
      obtain ⟨x4, x4h⟩ := h4 _ as_root4

      exact ⟨x3, x4, x3h.symm, x4h.symm⟩
      · ring
      · ring

    -- the sum of the roots is -p
    have sum_eq_p : x1 + x2 = -p := by
      rw [x1h, x2h]
      ring

    -- so p is an integer
    obtain ⟨pz, ph⟩ : ∃ z : ℤ, z = p := by
      exists -(x1 + x2)
      push_cast
      exact neg_eq_iff_eq_neg.mpr sum_eq_p

    -- difference of the roots is D1
    have sub_eq_D1 : x1 - x2 = D1 := by
      rw [x1h, x2h]
      ring

    -- so D1 is an integer
    obtain ⟨D1z, D1h⟩ : ∃ z : ℤ, z = D1 := by
      exists (x1 - x2)
      push_cast
      exact sub_eq_D1

    -- similarly, from the second equation we'll show that D2 is an integer

    -- difference of the roots is D2
    have sum_eq_D2 : x3 - x4 = D2 := by
      rw [x3h, x4h]
      ring

    -- so D2 is an integer
    obtain ⟨D2z, D2h⟩ : ∃ z : ℤ, z = D2 := by
      exists (x3 - x4)
      push_cast
      exact sum_eq_D2

    -- we can split up the polynomial x ^ 2 + p * x + q into (x - x1) * (x - x2)
    have split : (X ^ 2 + C p * X + C q) = (X - C (x1 : ℝ)) * (X - C (x2 : ℝ)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, map_intCast, eval_sub, eval_intCast]
      rw [x1h, x2h]
      have morph : (x - (-p + D1) / 2) * (x - (-p - D1) / 2) = ((x + (p / 2) - (D1 / 2))) * ((x + (p / 2) + (D1 / 2))) := by
        congr 1 <;> ring

      rw [morph, mul_comm (x + p / 2 - D1 / 2), ←sq_sub_sq, div_pow]
      unfold D1
      rw [Real.sq_sqrt D1_pos]
      unfold discrim
      ring

    -- then we see that the only roots of x ^ 2 + p * x + q are x1 and x2
    have roots : (X ^ 2 + C p * X + C q).roots = {(x1 : ℝ), (x2 : ℝ)} := by
      have ne_zero : (X - C (x1 : ℝ)) * (X - C (x2 : ℝ)) ≠ 0
        := mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)

      rw [split, Polynomial.roots_mul ne_zero, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
      norm_num

    -- We recall Vieta's formulas for monic quadratics
    have vieta : ∀ {a b c d : ℝ}, (X ^ 2 + C a * X + C b).roots = {c, d} → (b = c * d ∧ a = -(c + d)) := by
      intro a b c d h
      -- let p be the polynomial x ^ 2 + a * x + b
      let p := (1 * X ^ 2 + C a * X + C b)

      -- and the roots be c and d
      convert_to p.roots = {c, d} at h
      · unfold p
        rw [one_mul]

      -- then p has degree 2
      have degree : p.natDegree = 2 := Polynomial.natDegree_quadratic (by norm_num)

      -- and as many roots as degree
      have roots_card : p.roots.card = p.natDegree := by
        rw [degree, h]
        norm_num

      -- 0th coefficient of p is b, 1st coefficient of p is a
      have coeff_0 : p.coeff 0 = b := by unfold p; norm_num
      have coeff_1 : p.coeff 1 = a := by unfold p; norm_num

      -- p has a leading coefficient of 1
      have leading : p.leadingCoeff = 1 := Polynomial.leadingCoeff_quadratic (by norm_num)

      -- 0 and 1 are less than or equal to the degree, so it makes sense to talk about the 0th and 1st coefficient
      have zero_le : 0 ≤ p.natDegree := by linarith
      have one_le : 1 ≤ p.natDegree := by linarith

      constructor
      -- apply the general form of Vieta's formula to the 0th coefficient of p
      · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card zero_le

        -- simplifying we get b = c * d
        simpa only [coeff_0, leading, degree, tsub_zero, even_two, Even.neg_pow, one_pow, mul_one,
          Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, Nat.reduceAdd,
          Multiset.card_singleton, Nat.one_lt_ofNat, Multiset.powersetCard_eq_empty,
          Multiset.powersetCard_one, Multiset.map_singleton, zero_add, Multiset.prod_cons,
          Multiset.prod_singleton, Multiset.sum_singleton, one_mul] using vieta
      -- apply the general form of Vieta's formula to the 1st coefficient of p
      · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card one_le
        -- simplifying we get a = -(c + d)
        simp only [coeff_1, leading, degree, Nat.add_one_sub_one, pow_one, mul_neg, mul_one,
          Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, zero_add,
          Multiset.powersetCard_one, Multiset.map_singleton, Multiset.powersetCard_zero_left,
          Multiset.cons_zero, Multiset.singleton_add, Multiset.map_cons, Multiset.prod_singleton,
          Multiset.sum_cons, Multiset.sum_singleton, neg_mul, one_mul, neg_add_rev] at vieta
        linarith

    -- apply it to our case
    have ⟨vieta_1, vieta_2⟩ := vieta roots

    -- then we see that q is an integer
    obtain ⟨qz, qh⟩ : ∃ z : ℤ, z = q := by
      exists (x1 * x2)
      rw [vieta_1]
      norm_cast

    -- we have that D1 ^ 2 = p ^ 2 - 4 * q, where every term is an integer
    have D1_sq : D1z ^ 2 = pz ^ 2 - 4 * qz := by
      rify
      rw [D1h, ph, qh]
      simp only [D1, D1_pos, Real.sq_sqrt]
      unfold discrim
      ring

    -- we have that D2 ^ 2 = p ^ 2 + 4 * q, where every term is an integer
    have D2_sq : D2z ^ 2 = pz ^ 2 + 4 * qz := by
      rify
      rw [D2h, ph, qh]
      simp only [D2, D2_pos, Real.sq_sqrt]
      unfold discrim
      ring

    -- 2 is not zero
    have two_ne_zero : 2 ≠ 0 := by omega

    -- D1 has the same parity as p
    have D1_parity : Even D1z ↔ Even pz := by
      -- 4 * q is even
      have mul_four_even : Even (4 * qz) := by
        convert_to Even (2 * (2 * qz))
        · ring
        exact even_two_mul (2 * qz)

      -- D1 ^ 2 = p ^ 2 - 4 * q, so they must have the same parity
      rw [(Int.even_pow' two_ne_zero).symm, D1_sq]
      simp only [Int.even_sub, mul_four_even, iff_true]
      exact (Int.even_pow' two_ne_zero)

    -- D2 has the same parity as p
    have D2_parity : Even D2z ↔ Even pz := by
      -- 4 * q is even
      have mul_four_even : Even (4 * qz) := by
        convert_to Even (2 * (2 * qz))
        · ring
        exact even_two_mul (2 * qz)

      -- D2 ^ 2 = p ^ 2 + 4 * q, so they must have the same parity
      rw [(Int.even_pow' two_ne_zero).symm, D2_sq]
      simp only [Int.even_add, mul_four_even, iff_true]
      exact (Int.even_pow' two_ne_zero)

    -- so D1 has the same parity as D2
    have D1D2_parity : Even D1z ↔ Even D2z := D1_parity.trans D2_parity.symm


    -- add equations for D1 ^ 2 and D2 ^ 2
    have added : 2 * pz ^ 2 = D1z ^ 2 + D2z ^ 2 := by linarith

    -- isolate p ^ 2 on LHS
    have p_sq : pz ^ 2 = (D1z ^ 2 + D2z ^ 2) / 2 := by
      refine Int.eq_ediv_of_mul_eq_right ?_ added
      -- 2 ≠ 0
      norm_num

    -- rewrite RHS in a form of a ^ 2 + b ^ 2
    have split : (D1z ^ 2 + D2z ^ 2) / 2 = ((D1z + D2z) / 2) ^ 2 + ((D1z - D2z) / 2) ^ 2 := by
      have even_sub : Even (D1z - D2z) := by
        rw [Int.even_sub]
        exact D1D2_parity
      have even_add : Even (D1z + D2z) := by
        rw [Int.even_add]
        exact D1D2_parity

      have even_sq_add : Even (D1z ^ 2 + D2z ^ 2) := by
        rw [Int.even_add, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero]
        exact D1D2_parity

      -- 2 ∣ D1 - D2
      have two_dvd_sub := even_iff_two_dvd.mp even_sub
      -- 2 ∣ D1 + D2
      have two_dvd_add := even_iff_two_dvd.mp even_add
      -- 2 ∣ D1 ^ 2 + D2 ^ 2
      have two_dvd_sq_add := even_iff_two_dvd.mp even_sq_add

      -- consider the equation over the reals
      rify
      -- the integer 2 considered as a rational is still not 0
      have cast_two_ne_zero : ((2 : ℤ) : ℝ) ≠ 0 := by norm_num

      -- use divisibility lemmas to to show that casting to reals distribute over the divisions
      rw [Int.cast_div two_dvd_sub cast_two_ne_zero,
        Int.cast_div two_dvd_add cast_two_ne_zero,
        Int.cast_div two_dvd_sq_add cast_two_ne_zero]
      push_cast

      -- then when we just have reals and operations over reals, we see that it's true
      ring_nf

    -- so we have that p ^ 2 = ((D1 + D2) / 2) ^ 2 + ((D1 - D2) / 2) ^ 2
    -- where RHS terms are integers
    exists (D1z + D2z) / 2, (D1z - D2z) / 2
    rw [←ph]
    norm_cast
    exact p_sq.trans split