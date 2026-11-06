import Mathlib

/-The polynomial $x^3 - 3x^2 + 4x - 1$ is a factor of $x^9 + px^6 + qx^3 + r.$  Enter the ordered triple $(p,q,r).$-/
theorem algebra_22609 {p q r : ℝ} (h : Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X - (1 : Polynomial ℝ) ∣ (Polynomial.X ^ 9 + Polynomial.C p * Polynomial.X ^ 6 + Polynomial.C q * Polynomial.X ^ 3 + Polynomial.C r)) :
    p = 6 ∧ q = 31 ∧ r = -1 := by
  -- set f := x^3 - 3x^2 + 4x - 1
  set f := Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X - (1 : Polynomial ℝ) with hf
  -- actually show that X ^ 3 ≡ 3 * X ^ 2 - 4 * X + 1 [ZMOD f]
  have eq3 (g h : Polynomial ℝ) (h1 : f ∣ h * Polynomial.X ^ 3 + g) : f ∣ h * (3 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) + g := by
    have h2 : f ∣ h * (Polynomial.X ^ 3 - f) + g := by
      rw [mul_sub]
      rw [sub_add_eq_add_sub]
      simp [dvd_sub, show f ∣ h * f by exact dvd_mul_left f h, h1]
    ring_nf at h2 ⊢
    exact h2

  -- show that X ^ 4 ≡ 5 * X ^ 2 - 11 * X + 3 [ZMOD f]
  have eq4 (g h : Polynomial ℝ) (h1 : f ∣ h * Polynomial.X ^ 4 + g) : f ∣ h * (5 * Polynomial.X ^ 2 - 11 * Polynomial.X + 3) + g := by
    -- substitute one of the X ^ 3
    replace h1 : f ∣ h * Polynomial.X * Polynomial.X ^ 3 + g := by
      ring_nf at h1 ⊢
      exact h1
    -- simplify the expression to the form of eq3
    apply eq3 at h1
    replace h1 : f ∣ h * 3 * Polynomial.X ^ 3 + (-h * 4 * Polynomial.X ^ 2 + h * Polynomial.X + g) := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 3
    apply eq3 at h1
    ring_nf at h1 ⊢
    exact h1

  -- show that X ^ 6 ≡ -5 * X ^ 2 - 11 * X + 4 [ZMOD f]
  have eq6 (g h : Polynomial ℝ) (h1 : f ∣ h * Polynomial.X ^ 6 + g) : f ∣ h * (-5 * Polynomial.X ^ 2 - 11 * Polynomial.X + 4) + g := by
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * Polynomial.X ^ 3 * Polynomial.X ^ 3 + g := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute one of the X ^ 3
    apply eq3 at h1
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * (3 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) * Polynomial.X ^ 3 + g := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 3
    apply eq3 at h1
    -- expand the expression
    replace h1 : f ∣ h * (9 * Polynomial.X ^ 4 - 24 * Polynomial.X ^ 3 + 22 * Polynomial.X ^ 2 - 8 * Polynomial.X + 1) + g := by
      ring_nf at h1 ⊢
      exact h1
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * 9 * Polynomial.X ^ 4 +(h * (-24 * Polynomial.X ^ 3 + 22 * Polynomial.X ^ 2 - 8 * Polynomial.X + 1) + g) := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute one of the X ^ 4
    apply eq4 at h1
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * (-24) * Polynomial.X ^ 3 + (h * 9 * (5 * Polynomial.X ^ 2 -11 * Polynomial.X + 3) + h * (22 * Polynomial.X ^ 2 - 8 * Polynomial.X + 1) + g) := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 3
    apply eq3 at h1
    ring_nf at h1 ⊢
    exact h1
  -- show that X ^ 9 ≡ -63 * X ^ 2 + 190 * X - 54 [ZMOD f]
  have eq9 (g h : Polynomial ℝ) (h1 : f ∣ h * Polynomial.X ^ 9 + g) : f ∣ h * (-63 * Polynomial.X ^ 2 + 190 * Polynomial.X - 54) + g := by
    -- simplify the expression to the form of eq6
    replace h1 : f ∣ h * Polynomial.X ^ 3 * Polynomial.X ^ 6 + g := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 6
    apply eq6 at h1
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * (-5 * Polynomial.X ^ 2 - 11 * Polynomial.X + 4) * Polynomial.X ^ 3 + g := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 3
    apply eq3 at h1
    -- expand the expression
    replace h1 : f ∣ h * (-15 * Polynomial.X ^ 4 - 13 * Polynomial.X ^ 3 + 51 * Polynomial.X ^ 2 - 27 * Polynomial.X + 4) + g := by
      ring_nf at h1 ⊢
      exact h1
    -- simplify the expression to the form of eq4
    replace h1 : f ∣ h * (-15) * Polynomial.X ^ 4 + (h * (-13) * Polynomial.X ^ 3 + h * 51 * Polynomial.X ^ 2 + h * (-27) * Polynomial.X + h * 4 + g) := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 4
    apply eq4 at h1
    -- simplify the expression to the form of eq3
    replace h1 : f ∣ h * (-13) * Polynomial.X ^ 3 + (h * (-15) * (5 * Polynomial.X ^ 2 - 11 * Polynomial.X + 3) + h * 51 * Polynomial.X ^ 2 + h * (-27) * Polynomial.X + h * 4 + g) := by
      ring_nf at h1 ⊢
      exact h1
    -- substitute the X ^ 3
    apply eq3 at h1
    ring_nf at h1 ⊢
    exact h1
  -- show that X ^ 9 + p * X ^ 6 + q * X ^ 3 + r ≡ (-5*p + 3*q - 63) * X ^ 2 + (-11*p - 4*q + 190) * X + (4*p + q + r - 54) [ZMOD f]
  replace h : f ∣ ((-5 * Polynomial.C p + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 + (-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X + (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54)) := by
    -- simplify the expression to the form of eq9
    replace h : f ∣ 1 * Polynomial.X ^ 9 + (Polynomial.C p * Polynomial.X ^ 6 + Polynomial.C q * Polynomial.X ^ 3 + Polynomial.C r) := by
      ring_nf at h ⊢
      exact h
    -- substitute the X ^ 9
    apply eq9 at h
    -- simplify the expression to the form of eq6
    replace h : f ∣ Polynomial.C p * Polynomial.X ^ 6 + ((-63 * Polynomial.X ^ 2 + 190 * Polynomial.X - 54) + Polynomial.C q * Polynomial.X ^ 3 + Polynomial.C r) := by
      ring_nf at h ⊢
      exact h
    -- substitute the X ^ 6
    apply eq6 at h
    -- simplify the expression to the form of eq3
    replace h : f ∣ Polynomial.C q * Polynomial.X ^ 3 + (Polynomial.C p * (-5 * Polynomial.X ^ 2 - 11 * Polynomial.X + 4) + (-63 * Polynomial.X ^ 2 + 190 * Polynomial.X - 54) + Polynomial.C r) := by
      ring_nf at h ⊢
      exact h
    -- substitute the X ^ 3 and expand
    apply eq3 at h
    ring_nf at h ⊢
    exact h

  -- set g := (-5 * p + 3 * q - 63) * X ^ 2 + (-11 * p - 4 * q + 190) * X + (4 * p + q + r - 54)
  set g := (-5 * Polynomial.C p + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 + (-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X + (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54) with hg
  clear eq3 eq4 eq6 eq9
  -- this part, we want to show that g = 0
  -- firstly show that degree of f is 3
  have degreef : f.natDegree = 3 := by
    simp [hf]
    -- show that degree of X ^ 3 - 3 * X ^ 2 is 3
    have degree : (Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 3 := by
      calc
        (Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 : Polynomial ℝ).natDegree = (Polynomial.X ^ 3 : Polynomial ℝ).natDegree := by
          apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          calc
            (Polynomial.C 3 * Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 2 := by simp [Polynomial.natDegree_X_pow]
            _ < 3 := by norm_num
            _ = (Polynomial.X ^ 3 : Polynomial ℝ).natDegree := by rw [Polynomial.natDegree_X_pow]
        _ = 3 := by rw [Polynomial.natDegree_X_pow]
    -- show that degree of X ^ 3 - 3 * X ^ 2 + 4 * X is 3
    replace degree : (Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + 4 * Polynomial.X : Polynomial ℝ).natDegree = 3 := by
      -- show that degree of 4 * X is 1
      have degree₁ : (4 * Polynomial.X : Polynomial ℝ).natDegree = 1 := by
        simp [Polynomial.natDegree_X_pow]
      -- combine the degree of X ^ 3 - 3 * X ^ 2 and 4 * X
      nth_rewrite 2 [<-degree]
      apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
      rw [degree₁, degree]
      norm_num
    -- finally show that degree of X ^ 3 - 3 * X ^ 2 + 4 * X - 1 is 3
    nth_rewrite 2 [<-degree]
    apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
    simp [Polynomial.natDegree_C]
    rw [degree]
    norm_num

  -- show that degree of g is at most 2
  have degreeg : g.natDegree ≤ 2 := by
    -- show that degree of (-5 * p + 3 * q - 63) * X ^ 2 is at most 2
    have degree2 : ((-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
      calc -- first split the multiplication
        ((-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ (-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63 : Polynomial ℝ).natDegree + (Polynomial.X ^ 2 : Polynomial ℝ).natDegree := by apply Polynomial.natDegree_mul_le
        _ ≤ 2 := by
          -- rewrite the degree of X ^ 2
          rw [Polynomial.natDegree_X_pow]
          -- show that the degree of (-5 * p + 3 * q - 63) is at most 0
          -- first show that the degree of -5 * p is at most 0
          have degree₀ : (-(5 * Polynomial.C p) : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-(5 * Polynomial.C p) : Polynomial ℝ).natDegree = (5 * Polynomial.C p : Polynomial ℝ).natDegree := by
                simp [Polynomial.natDegree_neg]
              _ ≤ (5 : Polynomial ℝ).natDegree + (Polynomial.C p : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_mul_le
              _ = 0 := by
                simp [Polynomial.natDegree_C]
          -- show that the degree of 3 * q is at most 0
          have degree₁ : (3 * Polynomial.C q : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (3 * Polynomial.C q : Polynomial ℝ).natDegree ≤ (3 : Polynomial ℝ).natDegree + (Polynomial.C q : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_mul_le
              _ = 0 := by
                simp [Polynomial.natDegree_C]
          -- combine both of above, show that the degree of (-5 * p + 3 * q) is at most 0
          have degree₂ : (-(5 * Polynomial.C p) + 3 * Polynomial.C q : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-(5 * Polynomial.C p) + 3 * Polynomial.C q : Polynomial ℝ).natDegree ≤ max (-(5 * Polynomial.C p) : Polynomial ℝ).natDegree (3 * Polynomial.C q : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_add_le
              _ ≤ 0 := by
                rw [Nat.max_le]; tauto
          -- show that the degree of (-5 * p + 3 * q - 63) is at most 0
          have degree₃ : (-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63 : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63 : Polynomial ℝ).natDegree ≤ max (-(5 * Polynomial.C p) + 3 * Polynomial.C q : Polynomial ℝ).natDegree (63 : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_sub_le
              _ ≤ 0 := by
                rw [Nat.max_le]
                have _ : (63 : Polynomial ℝ).natDegree ≤ 0 := by
                  simp [Polynomial.natDegree_C]
                tauto
          simp [degree₃]

    -- show that degree of (-11 * p - 4 * q + 190) * X is at most 1
    have degree1 : ((-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X).natDegree ≤ 1 := by
      calc -- first split the multiplication
        ((-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X : Polynomial ℝ).natDegree ≤ ((-11 * Polynomial.C p - 4 * Polynomial.C q + 190) : Polynomial ℝ).natDegree + (Polynomial.X : Polynomial ℝ).natDegree := by
          apply Polynomial.natDegree_mul_le
        _ ≤ 1 := by
          -- rewrite the degree of X
          rw [Polynomial.natDegree_X]
          -- show that the degree of -11 * p is at most 0
          have degree₀ : (-11 * Polynomial.C p : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-11 * Polynomial.C p : Polynomial ℝ).natDegree ≤ (-11 : Polynomial ℝ).natDegree + (Polynomial.C p : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_mul_le
              _ = 0 := by
                simp [Polynomial.natDegree_C]
          -- show that the degree of 4 * q is at most 0
          have degree₁ : (4 * Polynomial.C q : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (4 * Polynomial.C q : Polynomial ℝ).natDegree ≤ (4 : Polynomial ℝ).natDegree + (Polynomial.C q : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_mul_le
              _ = 0 := by
                simp [Polynomial.natDegree_C]
          -- combine both of above, show that the degree of (-11 * p - 4 * q) is at most 0
          have degree₂ : (-11 * Polynomial.C p - 4 * Polynomial.C q : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-11 * Polynomial.C p - 4 * Polynomial.C q : Polynomial ℝ).natDegree ≤ max (-11 * Polynomial.C p : Polynomial ℝ).natDegree (4 * Polynomial.C q : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_sub_le
              _ ≤ 0 := by
                rw [Nat.max_le]; tauto
          -- show that the degree of (-11 * p - 4 * q + 190) is at most 0
          have degree₃ : (-11 * Polynomial.C p - 4 * Polynomial.C q + 190 : Polynomial ℝ).natDegree ≤ 0 := by
            calc
              (-11 * Polynomial.C p - 4 * Polynomial.C q + 190 : Polynomial ℝ).natDegree ≤ max (-11 * Polynomial.C p - 4 * Polynomial.C q : Polynomial ℝ).natDegree (190 : Polynomial ℝ).natDegree := by
                apply Polynomial.natDegree_add_le
              _ ≤ 0 := by
                rw [Nat.max_le]
                have _ : (190 : Polynomial ℝ).natDegree ≤ 0 := by
                  simp [Polynomial.natDegree_C]
                tauto
          -- finally show that the degree of (-11 * p - 4 * q + 190) * X is at most 1
          ring_nf at degree₃ ⊢
          simp [degree₃]

    -- show that degree of (4 * p + q + r - 54) is at most 0
    have degree0 : (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54 : Polynomial ℝ).natDegree ≤ 0 := by
      -- show that the degree of 4 * p is at most 0
      have degree₁ : (4 * Polynomial.C p : Polynomial ℝ).natDegree ≤ 0 := by
        calc
          (4 * Polynomial.C p : Polynomial ℝ).natDegree ≤ (4 : Polynomial ℝ).natDegree + (Polynomial.C p : Polynomial ℝ).natDegree := by
            apply Polynomial.natDegree_mul_le
          _ = 0 := by
            simp [Polynomial.natDegree_C]
      -- show that the degree of 4 * p + q is at most 0
      have degree₂ : (4 * Polynomial.C p + Polynomial.C q : Polynomial ℝ).natDegree ≤ 0 := by
        calc
          (4 * Polynomial.C p + Polynomial.C q : Polynomial ℝ).natDegree ≤ max (4 * Polynomial.C p : Polynomial ℝ).natDegree (Polynomial.C q : Polynomial ℝ).natDegree := by
            apply Polynomial.natDegree_add_le
          _ ≤ 0 := by
            rw [Nat.max_le]
            simp [degree₁, Polynomial.natDegree_C]
      --  show that the degree of 4 * p + q + r is at most 0
      have degree₃ : (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r : Polynomial ℝ).natDegree ≤ 0 := by
        calc
          (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r : Polynomial ℝ).natDegree ≤ max (4 * Polynomial.C p + Polynomial.C q : Polynomial ℝ).natDegree (Polynomial.C r : Polynomial ℝ).natDegree := by
            apply Polynomial.natDegree_add_le
          _ ≤ 0 := by
            rw [Nat.max_le]
            have _ : (Polynomial.C r : Polynomial ℝ).natDegree ≤ 0 := by
              simp [Polynomial.natDegree_C]
            tauto
      -- show that the degree of 4 * p + q + r - 54 is at most 0
      have degree₄ : (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54 : Polynomial ℝ).natDegree ≤ 0 := by
        calc
          (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54 : Polynomial ℝ).natDegree ≤ max (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r : Polynomial ℝ).natDegree (54 : Polynomial ℝ).natDegree := by
            apply Polynomial.natDegree_sub_le
          _ ≤ 0 := by
            rw [Nat.max_le]
            have _ : (54 : Polynomial ℝ).natDegree ≤ 0 := by
              simp [Polynomial.natDegree_C]
            tauto
      -- finally show that the degree of (4 * p + q + r - 54) is at most 0
      exact degree₄
    -- combine the degree of (-5 * p + 3 * q - 63) * X ^ 2 and (-11 * p - 4 * q + 190) * X and (4 * p + q + r - 54)
    calc -- first split the addition
      g.natDegree ≤ max (((-5 * Polynomial.C p + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 + (-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X : Polynomial ℝ).natDegree) (4 * Polynomial.C p + Polynomial.C q + Polynomial.C r - 54 : Polynomial ℝ).natDegree := by
        rw [hg]
        apply Polynomial.natDegree_add_le
      _ ≤ 2 := by
        -- rewrite the function of max
        rw [Nat.max_le]
        refine ⟨?_, ?_⟩
        -- show that the degree of (-5 * p + 3 * q - 63) * X ^ 2 + (-11 * p - 4 * q + 190) is at most 2
        . calc -- first split the addition
            ((-5 * Polynomial.C p + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 + (-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X : Polynomial ℝ).natDegree ≤ max ((-5 * Polynomial.C p + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 : Polynomial ℝ).natDegree ((-11 * Polynomial.C p - 4 * Polynomial.C q + 190) * Polynomial.X : Polynomial ℝ).natDegree := by
              apply Polynomial.natDegree_add_le
            _ ≤ 2 := by
              -- rewrite the function of max
              rw [Nat.max_le]
              refine ⟨?_, ?_⟩
              -- actually use the degree of (-5 * p + 3 * q - 63) * X ^ 2 := degree2
              . ring_nf at degree2 ⊢
                exact degree2
                -- actually use the degree of (-11 * p - 4 * q + 190) * X := degree1
              . linarith only [degree1]
        -- show that the degree of 4 * p + q + r - 54 is at most 2
        . linarith only [degree0]

  -- finally show that g = 0
  have hg0 : g = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_natDegree_lt at h
    apply h
    linarith only [degreef, degreeg]

  -- from g = 0, we have three linaer equations
  -- eqaution 1 : show that -5 * p + 3 * q - 63 = 0
  have eq1 : -5 * p + 3 * q - 63 = 0 := by
    -- show that the coefficient of X ^ 2 is 0
    have eq : g.coeff 2 = 0 := by
      rw [hg0]
      simp
    rw [hg] at eq
    simp at eq
    -- convert the equation to the form of monomial
    have eq₁ : (Polynomial.monomial 2) (-5 * p + 3 * q - 63) = ((-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 : Polynomial ℝ) := by
      rw [<-Polynomial.C_mul_X_pow_eq_monomial]
      congr 1
      simp
      norm_cast
    rw [<-eq₁] at eq
    rw [Polynomial.coeff_monomial] at eq
    simp at eq
    ring_nf at eq ⊢
    exact eq

  -- equation 2 : show that -11 * p - 4 * q + 190 = 0
  have eq2 : -11 * p - 4 * q + 190 = 0 := by
    -- show that the coefficient of X is 0
    have eq : g.coeff 1 = 0 := by
      rw [hg0]
      simp
    rw [hg] at eq
    simp at eq
    -- convert the equation to the form of monomial
    have eq₁ : (Polynomial.monomial 2) (-5 * p + 3 * q - 63) = ((-(5 * Polynomial.C p) + 3 * Polynomial.C q - 63) * Polynomial.X ^ 2 : Polynomial ℝ) := by
      rw [<-Polynomial.C_mul_X_pow_eq_monomial]
      congr 1
      simp
      norm_cast
    rw [<-eq₁] at eq
    rw [Polynomial.coeff_monomial] at eq
    simp at eq
    ring_nf at eq ⊢
    exact eq

  -- equation 3 : show that 4 * p + q + r - 54 = 0
  have eq3 : 4 * p + q + r - 54 = 0 := by
    have eq : g.coeff 0 = 0 := by
      rw [hg0]
      simp
    rw [hg] at eq
    simp at eq
    exact eq

  -- solve the linear equations, we have p = 6, q = 31, r = -1
  -- first show that p = 6
  have hp : p = 6 := by
    calc
      p = (-53 * p) / (-53) := by ring_nf
      _ = (4 * (-5 * p + 3 * q - 63) + 3 * (-11 * p - 4 * q + 190) - 318) / (-53) := by ring_nf
      _ = 6 := by rw [eq1, eq2]; norm_num
  -- then show that q = 31
  have hq : q = 31 := by
    calc
      q = (3 * q) / 3 := by ring_nf
      _ = (5 * p + 63 + (-5 * p + 3 * q - 63)) / 3 := by ring_nf
      _ = 31 := by rw [eq1, hp]; norm_num
  -- finally show that r = -1
  have hr : r = -1 := by
    calc
      r = (54 - 4 * p - q + (4 * p + q + r - 54)) := by ring_nf
      _ = -1 := by rw [eq3, hp, hq]; norm_num
  tauto
