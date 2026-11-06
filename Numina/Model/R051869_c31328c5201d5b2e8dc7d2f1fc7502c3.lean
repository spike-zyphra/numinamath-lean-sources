import Mathlib

theorem algebra_11841 (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (h : ∀ n, (∑ i in Finset.Icc 1 n, a i) ^ 2 = ∑ i in Finset.Icc 1 n, (a i) ^ 3)
    (n : ℕ) (hn : n = 3) :
    (a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3) ∨
    (a 1 = 1 ∧ a 2 = 2 ∧ a 3 = -2) ∨
    (a 1 = 1 ∧ a 2 = -1 ∧ a 3 = 1) := by

  have h1 := h 1
  have h2 := h 2
  have h3 := h 3

  norm_num [Finset.sum_Icc_succ_top] at h1 h2 h3

  have ha1 : a 1 = 1 := by
    have eq := h1
    have h1' : a 1 ≠ 0 := ha 1
    -- Solving the equation $a_1^3 = a_1^2$ with $a_1 \neq 0$
    have : a 1 ^ 3 - a 1 ^ 2 = 0 := by
      nlinarith
    have : a 1 ^ 2 * (a 1 - 1) = 0 := by 
      ring_nf at this ⊢
      linarith

    cases (mul_eq_zero.mp this) with
    | inl h_eq_0 =>
      have : a 1 = 0 := by 
        nlinarith 
      exfalso 
      exact h1' (by linarith)
    | inr h_eq_1 =>
      have : a 1 = 1 := by linarith 
      exact this

  have ha2 : a 2 = 2 ∨ a 2 = -1 := by 
    rw [show a 1 = 1 by exact ha1] at h2
    have h2' : a 2 ≠ 0 := ha 2
    -- Solving the equation $(1 + a_2)^2 = 1 + a_2^3$ with $a_2 \neq 0$
    -- Expanding to get $a_2^3 - a_2^2 - 2a_2 = 0$
    -- Factor: $a_2(a_2^2 - a_2 - 2) = 0$
    -- Solving quadratic $a_2^2 - a_2 - 2 = 0$ gives roots $2$ or $-1$
    have h2'' : a 2 ^ 3 - a 2 ^ 2 - 2 * a 2 = 0 := by
      nlinarith 
    -- Factor out $a_2$: $a_2(a_2^2 - a_2 - 2) = 0$ 
    have h2''' : a 2 * (a 2 ^ 2 - a 2 - 2) = 0 := by 
      linarith [h2'']

    cases (mul_eq_zero.mp h2''') with
    | inl h0 => 
      exfalso 
      have : a 2 = 0 := by linarith 
      have hne : a 2 ≠ 0 := h2' 
      contradiction 
    | inr h_eq => 
      -- Solving quadratic $a_2^2 - a_2 - 2 = 0$
      have h_eq : a 2 ^ 2 - a 2 - 2 = 0 := by 
        linarith 
      have : (a 2 - 2) * (a 2 + 1) = 0 := by
        nlinarith 
      cases (mul_eq_zero.mp this) with
      | inl h3 => 
        -- $a_2 - 2 = 0$, so $a_2 = 2$
        have : a 2 = 2 := by linarith 
        left 
        exact this 
      | inr h4 => 
        -- $a_2 + 1 = 0$, so $a_2 = -1$
        have : a 2 = -1 := by linarith 
        right 
        exact this 

  cases ha2 with
  | inl ha2_2 => 
    -- Case where $a_2 = 2$
    rw [show a 1 = 1 by exact ha1, show a 2 = 2 by exact ha2_2] at h3
    -- Solving the equation $(3 + a_3)^2 = 9 + a_3^3$ with $a_3 \neq 0$
    have h3' : a 3 ≠ 0 := ha 3 
    have eq : a 3 ^ 3 - a 3 ^ 2 - 6 * a 3 = 0 := by 
      nlinarith
    -- Factor: $a_3(a_3^2 - a_3 - 6) = 0$
    have factored : a 3 * (a 3 ^ 2 - a 3 - 6) = 0 := by 
      linarith [eq]
    cases (mul_eq_zero.mp factored) with
    | inl h0 => 
      exfalso 
      have : a 3 = 0 := by linarith 
      contradiction 
    | inr h_eq_2 => 
      have h_eq : a 3 ^ 2 - a 3 - 6 = 0 := by 
        linarith 
      have factored_2 : (a 3 - 3) * (a 3 + 2) = 0 := by 
        nlinarith 
      cases (mul_eq_zero.mp factored_2) with
      | inl h4 => 
        have : a 3 = 3 := by linarith 
        left 
        exact ⟨by linarith, ha2_2, this⟩ 
      | inr h4 => 
        have : a 3 = -2 := by linarith 
        right 
        left 
        exact ⟨by linarith, ha2_2, this⟩ 
  | inr ha2_m1 => 
    -- Case where $a_2 = -1$
    rw [show a 1 = 1 by exact ha1, show a 2 = -1 by exact ha2_m1] at h3
    -- Solving the equation $a_3^2 = a_3^3$ with $a_3 \neq 0$
    have h3' : a 3 ≠ 0 := ha 3 
    have eq : a 3 ^ 3 - a 3 ^ 2 = 0 := by 
      nlinarith 
    have factored : a 3 ^ 2 * (a 3 - 1) = 0 := by 
      linarith [eq]
    cases (mul_eq_zero.mp factored) with
    | inl h0 => 
      have : a 3 = 0 := by 
        nlinarith 
      exfalso 
      contradiction 
    | inr h_eq => 
      have : a 3 = 1 := by linarith 
      right 
      right 
      exact ⟨by linarith, ha2_m1, this⟩