import Mathlib

/- Let $a, b$, and $c$ be real numbers such that

$$
|a - b| \geq |c|, \quad |b - c| \geq |a|, \quad \text{and} \quad |c - a| \geq |b|.
$$

Prove that one of the three numbers $a, b$, and $c$ is the sum of the other two. -/
theorem algebra_607573 {a b c : ℝ}
    (h₀ : |a - b| ≥ |c|) (h₁ : |b - c| ≥ |a|) (h₂ : |c - a| ≥ |b|) :
    a = b + c ∨ b = a + c ∨ c = a + b := by
  -- Step 1: Process the three absolute value inequalities, convert them to the form of difference of squares, and prove their non-negativity.
  have h₀' : (a - b + c) * (a - b - c) ≥ 0 := by
    -- Convert the absolute value inequality to a comparison of squares.
    have h_sq : (a - b) ^ 2 ≥ c ^ 2 := by
      nlinarith [abs_nonneg (a - b), abs_nonneg c, sq_abs (a - b), sq_abs c]
    -- Decompose the difference of squares into a product form.
    have h_sub : (a - b) ^ 2 - c ^ 2 ≥ 0 := by linarith
    -- Rewrite the expression and apply the non-negativity theorem.
    rw [sq, sq] at h_sub
    nlinarith [sq_nonneg (a - b + c), sq_nonneg (a - b - c)]
  have h₁' : (b - c + a) * (b - c - a) ≥ 0 := by
    -- Similarly process the second absolute value inequality.
    have h_sq : (b - c) ^ 2 ≥ a ^ 2 := by
      nlinarith [abs_nonneg (b - c), abs_nonneg a, sq_abs (b - c), sq_abs a]
    have h_sub : (b - c) ^ 2 - a ^ 2 ≥ 0 := by linarith
    rw [sq, sq] at h_sub
    nlinarith [sq_nonneg (b - c + a), sq_nonneg (b - c - a)]
  have h₂' : (c - a + b) * (c - a - b) ≥ 0 := by
    -- Similarly process the third absolute value inequality.
    have h_sq : (c - a) ^ 2 ≥ b ^ 2 := by
      nlinarith [abs_nonneg (c - a), abs_nonneg b, sq_abs (c - a), sq_abs b]
    have h_sub : (c - a) ^ 2 - b ^ 2 ≥ 0 := by linarith
    rw [sq, sq] at h_sub
    nlinarith [sq_nonneg (c - a + b), sq_nonneg (c - a - b)]
  -- Step 2: Combine the three non-negative products to derive the non-positivity of their product.
  have h₃ : (a - b + c)^2 * (a + b - c)^2 * (a - b - c)^2 ≤ 0 := by
    -- Multiply the three non-negative products to obtain overall non-negativity.
    have h_product : (a - b + c) * (a - b - c) * (b - c + a) * (b - c - a) * (c - a + b) * (c - a - b) ≥ 0 := by
      nlinarith [mul_nonneg h₀' h₁', mul_nonneg (mul_nonneg h₀' h₁') h₂']
    -- Convert the product expression to the form of difference of squares and simplify.
    have h_sq1 : (a - b + c) * (a - b - c) = (a - b)^2 - c^2 := by ring
    have h_sq2 : (b - c + a) * (b - c - a) = (b - c)^2 - a^2 := by ring
    have h_sq3 : (c - a + b) * (c - a - b) = (c - a)^2 - b^2 := by ring
    have h_rewrite : (a - b + c) * (a - b - c) * (b - c + a) * (b - c - a) * (c - a + b) * (c - a - b) =
      -((a - b + c)^2 * (a + b - c)^2 * (a - b - c)^2) := by
      simp only [h_sq1, h_sq2, h_sq3]
      ring
    -- Apply the non-negativity theorem to derive the target inequality.
    nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c)]
  -- Step 3: Prove that the product must be zero, and then decompose to obtain linear relationships.
  have h₄ : (a - b + c)^2 * (a + b - c)^2 * (a - b - c)^2 = 0 := by
    -- Use the contradiction of non-negativity and non-positivity to determine that the product is zero.
    have h_nonneg : (a - b + c)^2 * (a + b - c)^2 * (a - b - c)^2 ≥ 0 := by
      have h1 : (a - b + c)^2 ≥ 0 := by exact sq_nonneg (a - b + c)
      have h2 : (a + b - c)^2 ≥ 0 := by exact sq_nonneg (a + b - c)
      have h3 : (a - b - c)^2 ≥ 0 := by exact sq_nonneg (a - b - c)
      exact mul_nonneg (mul_nonneg h1 h2) h3
    linarith [h₃, h_nonneg]
  -- Step 4: Decompose the condition of the product being zero to obtain three possible linear equations.
  rw [mul_eq_zero] at h₄
  rw [mul_eq_zero] at h₄
  cases' h₄ with h₅ h₆
  · cases' h₅ with h₇ h₈
    · -- Case 1: The first square term is zero, derive \( c = a - b \).
      rw [pow_eq_zero_iff] at h₇
      right
      left
      linarith  -- Apply linear arithmetic to verify the equation.
      linarith  -- Ensure the non-negativity of the square term.
    · -- Case 2: The second square term is zero, derive \( c = a + b \).
      rw [pow_eq_zero_iff] at h₈
      right 
      right
      linarith
      linarith
  · -- Case 3: The third square term is zero, derive \( a = b + c \).
    rw [pow_eq_zero_iff] at h₆
    left
    linarith
    linarith