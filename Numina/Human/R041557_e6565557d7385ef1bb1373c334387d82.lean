import Mathlib


/- 12th Irish 1999 Problem B3 Show that a^2 /(a+b) + b^2 /(b+c) + c^2 /(c+d) + d^2 /(d+a) ≥ 1/2 for positive reals a, b, c, d such that a + b + c + d = 1, and that we have equality iff a = b = c = d. -/
theorem inequalities_133965 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    1 / 2 ≤ a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ∧
    (1 / 2 = a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ↔
      (a = b ∧ b = c ∧ c = d))
  := by

    -- apply Cauchy-Schwartz to f = a / √(a + b), b / √(b + c), ...
    -- and g = √(a + b), √(b + c), ...
    let f := !₂[a / √(a + b), b / √(b + c), c / √(c + d), d / √(d + a)]
    let g := !₂[√(a + b), √(b + c), √(c + d), √(d + a)]

    have cauchy := @real_inner_mul_inner_self_le _ _ _ f g
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at cauchy

    -- ∑ i, f i * g i = 1
    have mul_sum_eq :  ∑ i : Fin 4, f i * g i = 1 := by
      simp only [Fin.sum_univ_four]
      unfold f g
      simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
        Matrix.cons_val_three]

      have div_mul_eq : ∀ {x y}, 0 < x → 0 < y → x / √(x + y) * √(x + y) = x := by
        intro x y xh yh
        apply div_mul_cancel₀
        positivity

      rw [div_mul_eq ha hb, div_mul_eq hb hc,
        div_mul_eq hc hd, div_mul_eq hd ha]
      exact h

    -- rewrite squares in sums
    have sum_pow : ∑ x : Fin 4, f x * f x = ∑ x : Fin 4, f x ^ 2 := by
      congr
      ext aa
      exact (pow_two (f aa)).symm

    have sum_pow_2 : ∑ x : Fin 4, g x * g x = ∑ x : Fin 4, g x ^ 2 := by
      congr
      ext aa
      exact (pow_two (g aa)).symm

    rw [mul_sum_eq, sum_pow, sum_pow_2] at cauchy

    -- ∑ i, f i ^ 2 equals our wanted RHS
    have sum_f_sq : (∑ i : Fin 4, f i ^ 2) = a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + d) + d^2 / (d + a) := by
      simp only [Fin.sum_univ_four]
      unfold f
      simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
        Matrix.cons_val_three]
      have eqq : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := by
        exact fun x => Eq.symm (Real.rpow_two x)
      rw [←Real.rpow_two, ←Real.rpow_two, ←Real.rpow_two, ←Real.rpow_two]
      repeat rw [Real.div_rpow (by positivity) (by positivity)]
      simp only [Real.rpow_two]
      repeat rw [Real.sq_sqrt (by positivity)]


    -- ∑ i, g i ^ 2 = 2
    have sum_g_sq : ∑ i : Fin 4, g i ^ 2 = 2 := by
      simp only [Fin.sum_univ_four]
      unfold g
      simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
        Matrix.cons_val_three]
      repeat rw [Real.sq_sqrt (by positivity)]
      convert_to 2 * (a + b + c + d) = 2
      · ring
      rw [h]
      exact mul_one 2

    -- convert cauchy inequality to our case
    rw [mul_one, sum_f_sq, sum_g_sq, ←div_le_iff₀ zero_lt_two] at cauchy

    constructor
    -- the inequality follows from the cauchy inequality
    · exact cauchy
    · constructor
      · intro eq_h
        -- f is not zero
        have f_ne_zero : f ≠ 0 := by
          -- assume the opposite
          by_contra f_h
          -- the the first element has to be equal to zero
          have zero_case := congrFun f_h 0

          -- either a = 0 ∨ √(a + b) = 0
          unfold f at zero_case
          simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, PiLp.zero_apply,
            div_eq_zero_iff] at zero_case
          cases' zero_case with h1 h2
          -- a < 0 and a = 0 is a contradiction
          · linarith only [h1, ha]
          -- if √(a + b) = 0, then a + b = 0
          · rw [Real.sqrt_eq_zero] at h2

            -- but a and b are positive, contradiction
            linarith only [h2, ha, hb]

            -- a + b is positive
            positivity

        -- g is not zero
        have g_ne_zero : g ≠ 0 := by
          -- assume the opposite
          by_contra g_h
          -- the the first element has to be equal to zero
          have zero_case := congrFun g_h 0
          -- then √(a + b) = 0
          unfold g at zero_case
          simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero,
            PiLp.zero_apply] at zero_case

          -- a + b = 0
          rw [Real.sqrt_eq_zero] at zero_case
          -- but a and b are positive, contradiction
          linarith only [zero_case, ha, hb]

          -- a + b is positive
          positivity

        -- equality case of Cauchy-Schwarz
        have eq_case := @norm_inner_eq_norm_iff ℝ (WithLp 2 (Fin 4 → ℝ)) _ _ _ _ _ f_ne_zero g_ne_zero
        simp only [norm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, OfNat.ofNat_ne_zero,
          ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs, one_div,
          ne_eq] at eq_case
        rw [mul_sum_eq, sum_g_sq, abs_one] at eq_case

        -- square root is equal to ^ (2⁻¹)
        have x_two : ∀ x : ℝ, √x = x ^ (2⁻¹ : ℝ) := by
          intro x
          rw [Real.sqrt_eq_rpow]
          congr
          exact (inv_eq_one_div 2).symm

        -- rewrite the Cauchy-Schwarz inequality to the form of our hypothesis
        rw [←x_two, ←x_two, ←Real.sqrt_mul' _ zero_le_two] at eq_case
        convert_to 1 = ((∑ x : Fin 4, f x ^ 2) * 2) ↔ ∃ r : ℝ, ¬r = 0 ∧ g = r • f at eq_case
        · have test := @Real.sqrt_eq_one ((∑ x : Fin 4, f x ^ 2) * 2)
          constructor
          · intro aa
            exact (test.mp aa.symm).symm
          · intro aa
            exact (test.mpr aa.symm).symm

        rw [←div_eq_iff, sum_f_sq] at eq_case

        -- then we have that ∃ r : ℝ, ¬r = 0 ∧ g = r • f
        simp only [eq_h, true_iff] at eq_case

        obtain ⟨r, rne, eqs⟩ := eq_case

        -- g = r * f gives us four equalities
        have eq_0 := congrFun eqs 0
        have eq_1 := congrFun eqs 1
        have eq_2 := congrFun eqs 2
        have eq_3 := congrFun eqs 3
        simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, PiLp.smul_apply,
          smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.cons_val_three, g,
          f] at eq_0 eq_1 eq_2 eq_3

        have eq_simp : ∀ {x y}, 0 < x → 0 < y → √(x + y) = r * (x / √(x + y)) → x + y = r * x := by
          intro x y xh yh hh
          apply_fun (· * √(x + y)) at hh
          field_simp at hh
          exact hh

        -- we get
        -- a + b = r * a
        -- b + c = r * b
        -- c + d = r * c
        -- d + a = r * d
        replace eq_0 := eq_simp ha hb eq_0
        replace eq_1 := eq_simp hb hc eq_1
        replace eq_2 := eq_simp hc hd eq_2
        replace eq_3 := eq_simp hd ha eq_3

        -- add together all equalities
        have r_eq : 2 * (a + b + c + d)
          = r * (a + b + c + d) := by
            linarith

        -- so r = 2
        replace r_eq : r = 2 := by
          rw [h] at r_eq
          linarith only [r_eq]

        subst r
        -- from a + b = 2 * a, we have a = b
        have a_eq_b : a = b := by linarith only [eq_0]

        -- from b + c = 2 * b, we have b = c
        have b_eq_c : b = c := by
          linarith only [eq_1]

        -- from c + d = 2 * c, we have c = d
        have c_eq_d : c = d := by
          linarith only [eq_2]

        -- we have all our equalities
        exact ⟨a_eq_b, b_eq_c, c_eq_d⟩

        -- we used that 2 is not 0
        exact (NeZero.ne' 2).symm

      -- equality is true when a = b = c = d
      · intro ⟨aa, bb, cc⟩
        rw [aa, bb, cc] at h ⊢
        -- every value is 1 / 4
        have d_eq : d = 1 / 4 := by linarith only [h]

        -- simplify
        rw [d_eq]
        ring