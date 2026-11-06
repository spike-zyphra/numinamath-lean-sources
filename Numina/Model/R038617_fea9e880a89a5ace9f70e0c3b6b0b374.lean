import Mathlib

theorem algebra_317531 (a : ℝ) :
    (∃! x : ℝ, x^3 - a * x^2 - 2 * a * x + a^2 - 1 = 0) ↔ a < 3 / 4 := by
  constructor
  · -- Forward direction: if there exists a unique real root, then a < 3/4
    intro h
    rcases h with ⟨x, hx₁, hx₂⟩
    have h1 : ∀ y : ℝ, y^3 - a * y^2 - 2 * a * y + a^2 - 1 = 0 → y = x := hx₂

    -- Factor the cubic polynomial
    have factorization : ∀ y : ℝ, y^3 - a * y^2 - 2 * a * y + a^2 - 1 = (y - (a + 1)) * (y^2 + y + 1 - a) := by
      intro y
      ring_nf
      <;> ring

    -- Apply factorization to our root x
    have hx₁' : (x - (a + 1)) * (x^2 + x + 1 - a) = 0 := by
      have h_eq := factorization x
      rw [h_eq] at hx₁
      linarith

    cases' mul_eq_zero.mp hx₁' with hx₁_a hx₁_b
    · -- Case where x - (a + 1) = 0, so x = a + 1
      have hx : x = a + 1 := by linarith
      -- Show that the quadratic factor has no real roots
      have discriminant_neg : 4 * a - 3 < 0 := by
        -- The quadratic y^2 + y +1 -a has discriminant 1 -4*(1*(-a +1)) = 1 +4*a -4 = 4*a -3
        -- Assume for contradiction that 4*a -3 ≥ 0
        by_contra h'
        push_neg at h'
        have h2 : ∃ y : ℝ, y^2 + y +1 - a = 0 := by
          have : ∃ y : ℝ, y^2 + y +1 - a = 0 := by
            use (-1 + Real.sqrt (4 * a - 3)) / 2
            ring_nf
            rw [Real.sq_sqrt (by nlinarith)]
            <;> linarith
          assumption
        rcases h2 with ⟨y, hy_eq⟩
        have hy_eq2 : y^3 - a * y^2 - 2 * a * y + a^2 - 1 = 0 := by
          have h_eq : y^3 - a * y^2 - 2 * a * y + a^2 - 1 = (y - (a + 1)) * (y^2 + y +1 - a) := by
            apply factorization
          rw [h_eq]
          have : y^2 + y +1 - a = 0 := by linarith
          rw [this]
          ring
          <;> nlinarith
        have hy_eq3 := h1 y hy_eq2
        -- This contradicts uniqueness since y ≠ x (a + 1)
        -- y^2 + y +1 -a =0, but y Ne a+1
        nlinarith [sq_pos_of_ne_zero (show (-1 : ℝ) ≠ 0 from by norm_num), hx, hy_eq, sq_nonneg (y - (a + 1)), sq_nonneg (y - a), sq_nonneg (x - y)]

      -- From discriminant_neg, we can solve for a
      linarith

    · -- Case where the quadratic factor = 0
      have h2₁ : x^2 + x +1 - a = 0 := by linarith
      have h2₂ : ∃ y : ℝ, y ≠ x ∧ y^3 - a * y^2 - 2 * a * y + a^2 - 1 = 0 := by
        have : ∃ y : ℝ, y ≠ x ∧ y^3 - a * y^2 - 2 * a * y + a^2 - 1 = 0 := by
          use a + 1
          constructor
          · -- Show a + 1 ≠ x
            nlinarith [sq_pos_of_ne_zero (show (-1 : ℝ) ≠ 0 from by norm_num), sq_nonneg (x - (a + 1)), sq_nonneg (x - 1), sq_nonneg (a + 1 - x), sq_nonneg (a - x), sq_nonneg (a - a / 4)]
          · -- Show (a + 1)^3 - a*(a + 1)^2 - 2*a*(a + 1) + a^2 -1 = 0
            nlinarith [sq_nonneg (x - (a + 1)), sq_nonneg (a + 1 - x), sq_nonneg (x - 1), sq_nonneg (x - a / 2), sq_nonneg (x - a / 3), sq_nonneg (x - a +1), sq_nonneg (a + 1 - a / 4), sq_nonneg (a - x), sq_nonneg (a -1), sq_nonneg (x -1)]
        assumption

      rcases h2₂ with ⟨y, hy_ne, hy_eq⟩
      -- Contradicts uniqueness
      exfalso
      apply hy_ne
      apply h1 y hy_eq

  · -- Backward direction: if a < 3/4, then there exists a unique real root
    intro h
    use a + 1
    constructor
    · -- Show that a + 1 is indeed a root
      ring_nf
    · -- Show that it is unique
      intro y hy_eq
      have factorization : ∀ z : ℝ, z^3 - a * z^2 - 2 * a * z + a^2 - 1 = (z - (a + 1)) * (z^2 + z + 1 - a) := by
        intro z
        ring_nf
      have hy_eq' : (y - (a + 1)) * (y^2 + y + 1 - a) = 0 := by
        have h_eq : y^3 - a * y^2 - 2 * a * y + a^2 - 1 = (y - (a + 1)) * (y^2 + y + 1 - a) := by
          apply factorization
        rw [h_eq] at hy_eq
        linarith
      cases' mul_eq_zero.mp hy_eq' with h_a h_b
      · -- Case where y - (a + 1) = 0
        -- Thus y = a + 1 
        linarith
      · -- Case where the quadratic factor = 0
        -- We need to show this has no real roots
        have : y^2 + y + 1 - a = 0 := by linarith
        have discriminant_neg : 4 * a - 3 < 0 := by linarith
        -- Contradicts because discriminant is negative
        nlinarith [sq_nonneg (y + 1 / 2), sq_nonneg (y +1), sq_nonneg (y - a), sq_nonneg (y - a / 2), sq_nonneg (y -1), sq_nonneg (y - a +1), sq_nonneg (y - a -1)]
      all_goals nlinarith