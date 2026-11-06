import Mathlib
/- Theorem: Given a real number m, if there exist two distinct real roots x₁ and x₂ 
that satisfy the same quadratic equation and the sum of their absolute values is 2,
then m must be 0 or √2.-/
theorem algebra_301437 (m : ℝ) (h : ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ 3*x₁^2 - 6*(m-1)*x₁ + m^2 + 1 = 0 ∧
    3*x₂^2 - 6*(m-1)*x₂ + m^2 + 1 = 0 ∧ |x₁| + |x₂| = 2) :
    m = 0 ∨ m = Real.sqrt 2 := by 

  -- Use the existential hypothesis to extract values x₁, x₂ and the assumptions
  rcases h with ⟨x₁, x₂, h_ne, h₁, h₂, h_abs⟩

  -- Subtract the two quadratic equations to eliminate m² + 1
  -- This gives a linear relation between x₁ and x₂
  have h_sub : 3 * (x₁^2 - x₂^2) - 6 * (m - 1) * (x₁ - x₂) = 0 := by linarith

  -- From the above, deduce x₁ + x₂ = 2(m - 1)
  have h_sum : x₁ + x₂ = 2 * (m - 1) := by
    -- Use x₁ ≠ x₂ to ensure x₁ - x₂ ≠ 0 (we can divide by it)
    have h1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr h_ne

    -- Use the identity a² - b² = (a + b)(a - b)
    have h2 : 3 * (x₁ + x₂) - 6 * (m - 1) = 0 := by
      have h3 : x₁^2 - x₂^2 = (x₁ + x₂) * (x₁ - x₂) := by ring
      rw [h3] at h_sub

      -- Rearranged form shows a factorization
      have : (x₁ + x₂) * (x₁ - x₂) * 3 - 6 * (m - 1) * (x₁ - x₂) = 0 := by linarith
      have : (x₁ - x₂) * (3 * (x₁ + x₂) - 6 * (m - 1)) = 0 := by linarith

      -- Solve the product = 0: either x₁ - x₂ = 0 or other factor = 0
      cases' (mul_eq_zero.mp this) with h4 h5
      · -- Case: x₁ - x₂ = 0 contradicts our assumption
        exfalso
        exact h_ne (by linarith)
      · -- Case: the remaining factor = 0
        linarith
    -- Finish deducing x₁ + x₂ = 2(m - 1)
    linarith

  -- Case analysis based on sign of x₁
  by_cases h_x1 : x₁ ≥ 0

  · -- Case 1: x₁ ≥ 0
    by_cases h_x2 : x₂ ≥ 0

    · -- Subcase 1.1: both x₁ and x₂ are non-negative
      -- Replace abs with identity
      rw [abs_of_nonneg h_x1, abs_of_nonneg h_x2] at h_abs

      -- Since both are ≥ 0, x₁ + x₂ = 2, and from h_sum, m = 2
      have hm : m = 2 := by linarith

      -- Plug into original equation and simplify
      have h1 : 3 * x₁^2 - 6 * (m - 1) * x₁ + m^2 + 1 = 0 := h₁
      rw [hm] at h1

      -- Check the resulting quadratic has no solution using square completion
      have : x₁^2 - 2 * x₁ + 5 / 3 = 0 := by 
        nlinarith

      -- Since (x₁ - 1)^2 ≥ 0, contradiction arises
      have : (x₁ - 1)^2 ≥ 0 := by apply sq_nonneg
      nlinarith

    · -- Subcase 1.2: x₁ ≥ 0, x₂ < 0
      -- Handle absolute value correctly
      rw [abs_of_nonneg h_x1, abs_of_neg (lt_of_not_ge h_x2)] at h_abs

      -- From |x₁| + |x₂| = 2 and x₂ < 0, derive difference and sum
      have h_eq : x₁ - x₂ = 2 := by linarith
      have h2 : x₁ + x₂ = 2 * (m - 1) := h_sum

      -- Solve linear system to express x₁ and x₂ in terms of m
      have eq1 : x₁ = m := by linarith
      have eq2 : x₂ = m - 2 := by linarith [h2, h_eq]

      -- Plug into the original equation
      rw [eq1] at h₁

      -- Reduce to a square expression
      nlinarith [sq_nonneg (m - 3 / 2)]

  · -- Case 2: x₁ < 0
    by_cases h_x2 : x₂ ≥ 0

    · -- Subcase 2.1: x₁ < 0, x₂ ≥ 0
      -- Similar to previous subcase
      rw [abs_of_neg (lt_of_not_ge h_x1), abs_of_nonneg h_x2] at h_abs

      -- Use |x₁| + |x₂| = 2 to get equations
      have h_eq : -x₁ + x₂ = 2 := by linarith
      have h2 : x₁ + x₂ = 2 * (m - 1) := h_sum

      -- Solve for x₁, x₂ in terms of m
      have eq1 : x₂ = m := by linarith
      have eq2 : x₁ = m - 2 := by linarith [h2, h_eq]

      -- Substitute into equation
      rw [eq2] at h₁

      -- Reduce and apply square non-negativity
      nlinarith [sq_nonneg (m - 3 / 2)]

    · -- Subcase 2.2: both x₁ < 0 and x₂ < 0
      -- Handle both as negative in absolute value
      rw [abs_of_neg (lt_of_not_ge h_x1), abs_of_neg (lt_of_not_ge h_x2)] at h_abs

      -- Then x₁ + x₂ = -2, so m = 0 from previous sum formula
      have hm : m = 0 := by linarith

      -- Conclude m = 0
      left
      exact hm
