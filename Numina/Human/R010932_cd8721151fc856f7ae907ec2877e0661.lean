import Mathlib

open Nat

-- By symmetry of x and y, we cut of the half of cases.
lemma half_cases (x y n : ℕ) :
    x ! + y ! = 3 ^ n * n !
  → x ≤ y
  → (x = 0 ∧ y = 2 ∧ n = 1)
  ∨ (x = 1 ∧ y = 2 ∧ n = 1) :=
by
  intro eq xlty
  have : n ≠ 0 := by
    intro c
    subst c
    simp at eq
    have : x ! ≥ 1 := factorial_pos _
    have : y ! ≥ 1 := factorial_pos _
    have : x ! + y ! > 1 := by apply lt_add_of_pos_of_le <;> assumption
    omega
  have n_pos : n ≥ 1 := by omega
  rcases em (x ≤ n) with (h|h)
  . -- We can rewrite the equation as $1 + \\frac{y!}{x!} = 3^n \\cdot \\frac{n!}{x!}$.
    have eq' : (1 + y ! / x ! : ℚ) = 3^n * n ! / x ! := by
      qify at eq
      apply_fun (fun (a : ℚ) => a * x !)
      ring_nf
      field_simp
      linarith
      apply mul_left_injective₀
      have : x ! > 0 := factorial_pos _
      qify at this
      linarith
    have xdn : x ! ∣ n ! := factorial_dvd_factorial h
    have : (n ! / x ! : ℕ) = (n ! / x ! : ℚ) := Rat.natCast_div n ! x ! xdn
    have : (3^n * n ! / x ! : ℕ) = (3^n * n ! / x ! : ℚ) := by
      have : x ! ∣ 3 ^ n * n ! := by
        exact dvd_mul_of_dvd_right xdn (3 ^ n)
      norm_cast
    have H : 3 ∣ 1 + y ! / x ! := by
      rw [←this] at eq'
      have : (1 + y ! / x ! : ℕ) = (1 + y ! / x ! : ℚ) := by
        have : x ! ∣ y ! := factorial_dvd_factorial xlty
        norm_cast
      have : (1 + y ! / x ! : ℕ) = 3 ^ n * n ! / x ! := by
        rw [eq'] at this
        exact Rat.natCast_inj.mp this
      rw [this]
      rw [Nat.mul_div_assoc]
      refine Dvd.dvd.mul_right ?_ (n ! / x !)
      apply dvd_pow_self 3
      assumption
      assumption
    have : y ≤ x + 2 := by
      sorry
    -- Now we have three subcases,
    -- y ∈ {x, x + 1, x + 2}
    rcases em (y = x) with (hy0|hy0)
    . rw [hy0] at eq
      rcases em (x = n) with (eqxn|eqxn)
      . rw [eqxn] at eq
        have h : 2 = 3^n := by
          ring_nf at eq
          have : n ! > 0 := factorial_pos n
          exact Nat.eq_of_mul_eq_mul_left this eq
        exfalso
        symm at h
        have : n = 0 ∨ n > 0 := by
          omega
        rcases this with (this|this)
        · rw [this] at h
          norm_num at h
        · have : 3 ∣ 3 ^ n := by
            apply dvd_pow
            · norm_num
            · linarith
          rw [h] at this
          norm_num at this
      have hx : x < n := by omega
      have : ¬ n ! ∣ 2 * x ! := by sorry
      exfalso
      apply this
      use 3 ^ n
      linarith
    rcases em (y = x + 1) with (hy1|hy1)
    . rw [hy1] at eq'
      have : ((x + 1)! / x ! : ℚ) = x + 1 := by
        have H : (x + 1)! / x ! = x + 1 := by
          rw [←Nat.ascFactorial_eq_div]
          simp[Nat.ascFactorial]
        have : x ! ∣ (x + 1)! := Dvd.intro_left x.succ rfl
        norm_cast
      rw [this, mul_div_assoc] at eq'
      norm_cast at eq'
      ring_nf at eq'
      rcases em (n > x) with (hnx | hnx)
      . sorry
      . have : n = x := by linarith
        rw [this] at eq'
        have h : 2 + x = 3 ^ x := by
          conv at eq' =>
            rhs
            conv => lhs; rw[show x ! / x ! = 1 by refine Nat.div_self ?_; exact factorial_pos x]
            simp
          exact eq'
        have : x = 1 := by
          have h1 : x ≥ 1 := by
            by_contra h2
            push_neg at h2
            have h3 : x = 0 := by
              omega
            rw [h3] at h
            norm_num at h
          -- Now we know x ≥ 1
          have this : x = 1 := by
            by_cases h5 : x ≤ 1
            -- x ≤ 1 and x ≥ 1 means x = 1
            omega
            -- x > 1 implies x ≥ 2
            push_neg at h5
            have h6 : x ≥ 2 := by
              omega
            have h7 : 3 ^ x > 2 + x := by
              have h8 : x ≥ 2 := h6
              have base := show 3 ^ 2 > 2 + 2 by norm_num
              have step : ∀ n, n ≥ 2 → 3 ^ n > 2 + n → 3 ^ (n + 1) > 2 + (n + 1) := by
                intro n hn h9
                have h10 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
                rw [h10]
                have h11 : 3 * 3 ^ n > 3 * (2 + n) := by linarith [h9]
                have h12 : 3 * (2 + n) > 2 + (n + 1) := by
                  nlinarith
                linarith
              exact Nat.le_induction base step x h8
            -- But we have 2 + x = 3 ^ x from hypothesis
            linarith
          assumption
        subst this
        tauto
    rcases em (y = x + 2) with (hy2|hy2)
    . subst hy2
      have : ((x + 2)! / x ! : ℚ) = (x + 2) * (x + 1) := by
        simp [factorial]
        rw [←mul_assoc, mul_div_assoc, div_self]
        linarith
        have := factorial_pos x
        qify at this
        linarith
      rw [this] at eq'
      sorry
    omega
  . -- The left case, x > n
    -- we can show y ∈ {n + 1, n + 2, n + 3}
    -- all of those cases are false, the proof is similar to the cases we shown
    exfalso
    sorry

theorem number_theory_8254 (x y n : ℕ) :
    x ! + y ! = 3 ^ n * n !
  ↔ (x = 0 ∧ y = 2 ∧ n = 1)
  ∨ (x = 2 ∧ y = 0 ∧ n = 1)
  ∨ (x = 1 ∧ y = 2 ∧ n = 1)
  ∨ (x = 2 ∧ y = 1 ∧ n = 1) :=
by
  constructor; swap
  . intro a
    repeat
      rcases a with (⟨xx,yy,nn⟩|a)
      subst xx yy nn
      rfl
    rcases a with ⟨xx,yy,nn⟩
    subst xx yy nn
    rfl
  . intro h
    rcases em (x ≤ y) with (a|a)
    . have := half_cases x y n ?_ a
      tauto
      assumption
    . have a' : y ≤ x := by omega
      have := half_cases y x n ?_ a'
      tauto
      rw [add_comm]
      assumption
