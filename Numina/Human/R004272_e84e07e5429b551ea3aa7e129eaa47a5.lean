import Mathlib

open Polynomial

/- Given a ≤ 1 / 4 and 0 ≤ b < 1 / 4, a * b < 1 / 16. -/
lemma mul_bound {a b : ℝ} (h2 : 0 ≤ b) (h3 : a ≤ 1 / 4) (h4 : b < 1 / 4)  : a * b < 1 / 16 := by
  nlinarith

/- 1. Let $a, b, c, a>0$ be integers such that the equation $a x^{2}+b x+c=0$ has two distinct solutions in the interval (0,1). Prove that $a \geq 5$ and find an example of such an equation for $a=5$. -/
theorem algebra_247153 (p : ℤ → ℤ → ℤ → Prop)
  (ph : p = fun a b c => 0 < a ∧ (∃ x y : ℝ, x ≠ y ∧ (x ∈ Set.Ioo 0 1) ∧ (y ∈ Set.Ioo 0 1) ∧ (C a * X ^ 2 + C b * X + C c).aroots ℝ = {x, y}))
  : (∀ a b c, (p a b c → 5 ≤ a)) ∧ (∃ b c, p 5 b c)
  := by
    -- prove each one separately
    split_ands
    · intro a b c h
      rw [ph] at h
      obtain ⟨ah, x, y, ne, x_mem, y_mem, roots⟩ := h

      -- consider the polynomial as a polynomial with real coefficients
      rw [Polynomial.aroots_def] at roots
      norm_num at roots
      convert_to (C (a : ℝ) * X ^ 2 + C (b : ℝ) * X + C (c : ℝ)).roots = {x, y} at roots

      -- call the polynomial p
      set p := (C (a : ℝ) * X ^ 2 + C (b : ℝ) * X + C (c : ℝ))

      -- p has degree 2
      have poly_degree : p.natDegree = 2 := by
        refine natDegree_quadratic ?_
        norm_cast
        linarith

      -- p has 2 roots
      have roots_card : p.roots.card = 2 := by
        rw [roots]
        norm_num

      -- so it's degree equals its roots
      have degree_eq_roots : p.roots.card = p.natDegree
        := by linarith

      -- so the polynomial splits
      have splits := Polynomial.splits_iff_card_roots.mpr degree_eq_roots

      -- so we can write it as a * ((x - x_1) * (x - x_2))
      have p_eq := Polynomial.eq_prod_roots_of_splits_id splits
      have leading_coeff : p.leadingCoeff = a := by
        refine leadingCoeff_quadratic ?_
        norm_cast
        linarith
      norm_num [roots, leading_coeff] at p_eq

      -- let f(0) be p evaluated at 0
      let f_0 := p.eval 0
      -- let f(1) be p evaluated at 1
      let f_1 := p.eval 1

      -- the roots are positive
      have x_pos : 0 < x := by
        norm_num at x_mem
        tauto
      have y_pos : 0 < y := by
        norm_num at y_mem
        tauto

      -- the roots are less than 1
      have x_lt : x < 1 := by
        norm_num at x_mem
        tauto
      have y_lt : y < 1 := by
        norm_num at y_mem
        tauto

      -- f(0) is positive
      have f_zero_pos : 0 < f_0 := by
        norm_num [f_0, p_eq]
        positivity

      -- f(1) is positive
      have f_one_pos : 0 < f_1 := by
        norm_num [f_1, p_eq]
        have sub_x_pos : 0 < 1 - x := by linarith
        have sub_y_pos : 0 < 1 - y := by linarith
        positivity

      -- f(0) is equal to c
      have f_0_eq : f_0 = c := by
        norm_num [f_0, p]

      -- f(1) is equal to a + b + c
      have f_1_eq : f_1 = (a + b + c : ℤ) := by
        norm_num [f_1, p]

      -- so because f(0) and f(1) are equal to integers, they are at least 1
      replace f_zero_pos : 1 ≤ f_0 := by
        rw [f_0_eq] at f_zero_pos ⊢
        norm_cast at f_zero_pos ⊢

      replace f_one_pos : 1 ≤ f_1 := by
        rw [f_1_eq] at f_one_pos ⊢
        norm_cast at f_one_pos ⊢

      -- so the product of f(0) and f(1) are at least 1
      have mul_pos : 1 ≤ f_0 * f_1 := one_le_mul_of_one_le_of_one_le f_zero_pos f_one_pos

      -- the product equals a ^ 2 * (x_0 - x_0 ^ 2) * (x_1 - x_1 ^ 2)
      have prod_eq : f_0 * f_1 = a ^ 2 * (x - x ^ 2) * (y - y ^ 2) := by
        norm_num [f_0, f_1, p_eq]
        ring

      -- the polynomial x - x ^ 2 is at most 1 / 4
      have sub_sq : ∀ i : ℝ, (i - i ^ 2) ≤ (1 / 4) := by
        intro i
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + (1 / 2) := by
          exists i - (1 / 2)
          linarith
        ring_nf
        norm_num
        positivity

      -- and if it's equal to 1 / 4, then x = 1 / 2
      have sub_sq_eq : ∀ {i : ℝ}, (i - i ^ 2) = (1 / 4) → i = 1 / 2 := by
        intro i
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + (1 / 2) := by
          exists i - (1 / 2)
          linarith
        ring_nf
        field_simp
        intro aa
        have sq_eq_zero : i' ^ 2 = 0 := by linarith
        norm_num at sq_eq_zero
        norm_num [sq_eq_zero]

      -- we have 0 < x_0 - x_0 ^ 2
      have x_bound' : 0 < x - x ^ 2 := by
        field_simp
        nlinarith

      -- and 0 < x_1 - x_1 ^ 2
      have y_bound' : 0 < y - y ^ 2 := by
        field_simp
        nlinarith

      -- then we have that (x_0 - x_0 ^ 2) * (x_1 - x_1 ^ 2) < 1 / 16
      have prod_lt : (x - x ^ 2) * (y - y ^ 2) < 1 / 16 := by
        have x_bound := sub_sq x
        have y_bound := sub_sq y

        -- consider when x_0 - x_0 ^ 2 < 1 / 4
        rcases lt_or_eq_of_le x_bound with x_lt | x_eq
        -- then the bound holds
        · rw [mul_comm]
          exact mul_bound (le_of_lt x_bound') (sub_sq y) x_lt

        -- so assume x_0 - x_0 ^ 2 = 1 / 4

        -- consider when x_1 - x_1 ^ 2 < 1 / 4
        rcases lt_or_eq_of_le y_bound with y_lt | y_eq
        -- then the bound holds
        · exact mul_bound (le_of_lt y_bound') (sub_sq x) y_lt

        -- so assume x_1 - x_1 ^ 2 = 1 / 4

        -- but then x_0 and x_1 are both equal to 1 / 2
        replace x_eq := sub_sq_eq x_eq
        replace y_eq := sub_sq_eq y_eq

        -- but they are different, contradiction
        rw [x_eq, y_eq] at ne
        contradiction

      -- group factors
      convert_to f_0 * f_1 = (a ^ 2) * ((x - x ^ 2) * (y - y ^ 2)) at prod_eq
      · ring

      -- we already have the lower bound of one
      have lower_bound : 1 ≤ (a ^ 2) * ((x - x ^ 2) * (y - y ^ 2)) := by linarith

      -- the right factor is positive
      have prod_pos : 0 < (x - x ^ 2) * (y - y ^ 2) := by positivity

      -- so 1 / ((x_0 - x_0 ^ 2) * (x_1 - x_1 ^ 2)) ≤ a ^ 2
      replace lower_bound : 1 / ((x - x ^ 2) * (y - y ^ 2)) ≤ a ^ 2 := by
        rw [div_le_iff₀ prod_pos]
        exact lower_bound

      -- we also have that 1 / (1 / 16) < 1 / ((x_0 - x_0 ^ 2) * (x_1 - x_1 ^ 2))
      have ltt : 1 / (1 / 16) < 1 / ((x - x ^ 2) * (y - y ^ 2))
        := one_div_lt_one_div_of_lt prod_pos prod_lt

      -- chaining and simplifying we have 16 < a ^ 2
      have a_bound : (16 : ℝ) < a ^ 2 := by
        norm_num at ltt lower_bound
        linarith

      -- so 4 < a
      replace a_bound : (4 : ℝ) < a := by
        have sqrt_sixteen : √16 = 4 := by
          have sixteen_eq : (16 : ℝ) = 4 * 4 := by norm_num
          rw [sixteen_eq]
          exact Real.sqrt_mul_self (by positivity)
        have sqrted := Real.sqrt_lt_sqrt ?_ a_bound
        rw [sqrt_sixteen, Real.sqrt_sq] at sqrted
        exact sqrted
        · positivity
        · positivity

      -- and a is an integer, so 5 ≤ a
      norm_cast at a_bound
    -- b = -5 and c = 1 works
    · exists -5, 1
      rw [ph]
      split_ands
      -- 0 < 5 = a is valid
      · omega
      -- the roots are (1 / 2) ± (1 / (2 * √5))
      · exists (1 / 2) - (1 / (2 * √5))
        exists (1 / 2) + (1 / (2 * √5))

        -- note that 1 < √5
        have one_lt_sqrt : 1 < √5 := by
          rw [Real.lt_sqrt]
          norm_num
          positivity

        -- then we check that the roots are valid
        split_ands
        -- the roots are different
        -- assume they are equal
        · by_contra eq
          -- then 1 / (2 * √5) is zero
          have diff_eq : 0 = 1 / (2 * √5) := by linarith
          -- but that's false
          norm_num at diff_eq
        -- 1 / 2 - 1 / (2 * √5) is positive
        · convert_to 0 < 1 / 2 * (1 - (1 / √5))
          · ring_nf
          norm_num
          rw [inv_lt_one₀]
          exact one_lt_sqrt
          positivity

        -- 1 / 2 - 1 / (2 * √5) less than 1
        · convert_to 1 / 2 * (1 - (1 / √5)) < 1
          · ring
          suffices : 0 < 1 / √5
          · linarith
          positivity
        -- 1 / 2 + 1 / (2 * √5) is positive
        · positivity
        -- 1 / 2 + 1 / (2 * √5) is less than 1
        · suffices : 1 / (2 * √5) < 1 / 2
          · linarith
          simp only [one_div]
          rw [inv_lt_inv₀]
          simp only [Nat.ofNat_pos, lt_mul_iff_one_lt_right]
          exact one_lt_sqrt
          positivity
          positivity
        -- the roots we supplied are the roots of 5 * x ^ 2 - 5 * x + 1
        -- the polynomial can be factored
        · have p_eq : (C 5 * X ^ 2 + C (-5) * X + C 1)
            = C 5 * ((X - C (1 / 2 - 1 / (2 * √5))) * (X - C (1 / 2 + 1 / (2 * √5))))
            := by
              apply Polynomial.funext
              intro x
              norm_num
              ring_nf
              rw [inv_pow]
              have five : √5 ^ 2 = 5 := Real.sq_sqrt (by positivity)
              rw [five]
              ring_nf
          -- consider it as a polynomial with real coefficients
          rw [Polynomial.aroots_def]
          norm_num
          convert_to (C (5 : ℝ) * X ^ 2 + C (-5 : ℝ) * X + C (1 : ℝ) : ℝ[X]).roots = {1 / 2 - 1 / (2 * √5), 1 / 2 + 1 / (2 * √5)}
          -- LHS is equal
          · congr
            norm_num
            exact rfl
          -- RHS is equal
          · norm_num

          -- calculate the roots of the polynomial
          rw [p_eq, Polynomial.roots_C_mul, Polynomial.roots_mul,
            Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
          -- which is equal to what we claimed
          norm_num

          -- the polynomial wasn't zero
          -- because it's 0th coefficient is non-zero
          · apply_fun (coeff · 0)
            norm_num
            field_simp
            split_ands <;> linarith
          -- five is not zero
          · linarith