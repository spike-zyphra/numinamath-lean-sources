import Mathlib

/- For any real number sequence $A=\left(a_{1}, a_{2}, a_{3}, \cdots\right)$, define $\Delta A$ as the sequence $\left(a_{2}-a_{1}, a_{3}-a_{2}, a_{4}-a_{3}, \cdots\right)$, where its $n$-th term is $a_{n+1}-a_{n}$. Assume that all terms of the sequence $\Delta (\Delta A)$ are 1, and $a_{19}=a_{92}=0$. Try to find $a_{1}$.
(1992 10th American Mathematical Invitational Problem 8) -/
theorem algebra_258055 (Δ : (ℕ → ℝ) → ℕ → ℝ)
  (hΔ : ∀ f n, Δ f n = f (n + 1) - f n)
  (A : ℕ → ℝ) (hΔΔA : ∀ n, Δ (Δ A) n = 1)
    (h1 : A 18 = 0) (h2 : A 91 = 0) : A 0 = 819
  := by
    -- ΔA increases by 1 every step
    have ΔA_eq : ∀ n, Δ A n = (Δ A 0) + n := by
      intro n
      -- prove by induction
      induction' n with k hk
      -- First value is equal to first value
      · simp only [CharP.cast_eq_zero, add_zero]
      -- use property of Δ
      · have eq := hΔ (Δ A) k
        -- use induction and that ΔΔA = 1
        rw [hΔΔA k, hk] at eq
        -- simplify
        push_cast
        -- reorder equations
        linarith only [eq]

    -- we have quadratic representation of A n
    have A_eq : ∀ n, A n = A 0 + n * (Δ A 0) + n * (n - 1) / 2 := by
      intro n
      -- prove by induction on n
      induction' n with k hk
      -- n = 0 can be simplified
      · simp only [CharP.cast_eq_zero, zero_mul, add_zero, zero_sub, mul_neg, mul_one, neg_zero,
          zero_div]
      -- use property of Δ
      · have eq := hΔ A k
        -- use induction and closed for mfor ΔA
        rw [ΔA_eq k, hk] at eq
        -- simplify
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        -- reorder equations
        linarith only [eq]

    -- Use A 18 = 0 to get an equality with two unknowns: A 0 and ΔA 0
    have apply_18 := A_eq 18
    -- simplify
    simp only [h1, Nat.cast_ofNat] at apply_18
    norm_num at apply_18

    -- Use A 91 = 0 to get an equality with two unknowns: A 0 and ΔA 0
    have apply_91 := A_eq 91
    -- simplify
    simp only [h2, Nat.cast_ofNat] at apply_91
    norm_num at apply_91

    -- we solve the linear system of equations to get A 0 = 819
    -- two unknowns and two equations means we can solve it
    linarith only [apply_18, apply_91]