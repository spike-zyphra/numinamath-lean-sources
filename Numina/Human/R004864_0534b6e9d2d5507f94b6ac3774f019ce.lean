import Mathlib
set_option maxHeartbeats 400000
/-
Vind alle drietallen $(x, y, z)$ van reële (maar niet noodzakelijk positieve) getallen die voldoen aan

$$
\begin{aligned}
3\left(x^{2}+y^{2}+z^{2}\right) & =1 \\
x^{2} y^{2}+y^{2} z^{2}+z^{2} x^{2} & =x y z(x+y+z)^{3} .
\end{aligned}
$$
-/

theorem algebra_604313 : {(x, y, z) : ℝ × ℝ × ℝ | 3 * (x ^ 2 + y ^ 2 + z ^ 2) = 1 ∧ x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 = x * y * z * (x + y + z) ^ 3} = {(0, 0, √3 / 3), (0, 0, -√3 / 3), (0, √3 / 3, 0), (0, -√3 / 3, 0), (√3 / 3, 0, 0), (-√3 / 3, 0, 0), (3⁻¹, 3⁻¹, 3⁻¹), (-3⁻¹, -3⁻¹, -3⁻¹)}:= by

  -- Extend the triple (x, y, z)
  ext ⟨x, y, z⟩
  constructor
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩

    -- Establish non-negativity of squared terms
    have g1 : (x * y - y * z) ^ 2 ≥ 0:= by positivity
    have g2 : (y * z - z * x) ^ 2 ≥ 0:= by positivity
    have g3 : (z * x - x * y) ^ 2 ≥ 0:= by positivity
    have g4 : (x - y) ^ 2 ≥ 0:= by positivity
    have g5 : (y - z) ^ 2 ≥ 0:= by positivity
    have g6 : (z - x) ^ 2 ≥ 0:= by positivity

    -- Key inequalities derived from the conditions
    have g7 : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 ≥ x * y * z * (x + y + z):= by linarith
    have g8 : 1 ≥ (x + y + z) ^ 2:= by rw [←h1] ; linarith

    -- Helper lemma for solving x² = 1/3
    have h3 : ∀ x : ℝ, x ^ 2 = 1 / 3 → x = -√3 / 3 ∨ x = √3 / 3:= by
      intro x hx
      have h3 : (√3 / 3) ^ 2 = 1 / 3:= by
        ring_nf
        norm_num
      rw [←h3] at hx
      replace hx : (x - √3 / 3) * (x + √3 / 3) = 0:= by linarith
      simp at hx
      rcases hx with hx | hx
      .
        right
        linarith
      .
        left
        linarith

    -- Helper lemma for solving x² = 1/9
    have h4 : ∀ x : ℝ, x ^ 2 = 1 / 9 → x = -3⁻¹ ∨ x = 3⁻¹:= by
      intro x hx
      replace hx : (x - 3⁻¹) * (x + 3⁻¹) = 0:= by
        ring_nf
        linarith
      simp at hx
      field_simp at hx
      rcases hx with hx | hx
      .
        right
        field_simp
        linarith
      .
        left
        field_simp
        linarith

    -- Main case analysis: check if equality holds in the inequality
    -- Case 1: When x²y² + y²z² + z²x² = xyz(x + y + z)
    by_cases g9 : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 = x * y * z * (x + y + z)
    .
      -- From the equality case, we can deduce that certain squared differences must be zero
      replace g1 : (x * y - y * z) ^ 2 = 0:= by linarith
      replace g2 : (y * z - z * x) ^ 2 = 0:= by linarith
      replace g3 : (z * x - x * y) ^ 2 = 0:= by linarith

      -- Since squares are zero, the terms themselves must be zero
      replace g1 : x * y - y * z = 0:= by exact pow_eq_zero g1
      replace g2 : y * z - z * x = 0:= by exact pow_eq_zero g2
      replace g3 : z * x - x * y = 0:= by exact pow_eq_zero g3

      -- Rearrange the equations to factor out common terms
      replace g1 : y * (x - z) = 0:= by linarith
      replace g2 : z * (y - x) = 0:= by linarith
      replace g3 : x * (z - y) = 0:= by linarith

      -- Apply zero product property: if ab = 0, then a = 0 or b = 0
      replace g1 : y = 0 ∨ x - z = 0:= by exact mul_eq_zero.mp g1

      -- Case analysis on y = 0 or x = z
      rcases g1 with g1 | g1
      .
        -- Case y = 0: leads to solutions where one coordinate is 0 and others are ±√3/3
        subst y
        simp at g2
        rcases g2 with g2 | g2
        .
          subst z
          ring_nf at h1
          specialize h3 x (by linarith)
          rcases h3 with h3 | h3
          all_goals
            subst x
            simp
        .
          subst x
          ring_nf at h1
          specialize h3 z (by linarith)
          rcases h3 with h3 | h3
          all_goals
            subst z
            simp
      .
        -- Case x = z: leads to solutions where all coordinates are ±1/3
        replace g1 : x = z:= by linarith
        rw [←g1] at g2 g3 h1
        simp at g2
        rcases g2 with g2 | g2
        .
          subst x z
          ring_nf at h1
          specialize h3 y (by linarith)
          simp
          rcases h3 with h3 | h3
          .
            right
            right
            right
            left
            exact h3
          .
            right
            right
            left
            exact h3
        .
          replace g2 : y = x:= by linarith
          simp
          rw [g2, g1] at h1 h2
          ring_nf at h1 h2
          replace h1 : z ^ 2 = 1 / 9:= by linarith
          rw [show z ^ 4 = (z ^ 2) ^ 2 by ring] at h2
          rw [show z ^ 6 = (z ^ 2) ^ 3 by ring] at h2
          rw [h1] at h2
          specialize h4 z h1
          rcases h4 with h4 | h4
          .
            right
            right
            right
            right
            right
            right
            right
            rw [g2, g1, h4]
            simp
          .
            right
            right
            right
            right
            right
            right
            left
            rw [g2, g1, h4]
            simp
    .
      -- Case 2: When strict inequality holds
      -- Prove this case leads to a contradiction
      replace g9 : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 > x * y * z * (x + y + z):= by
        by_contra H
        simp at H
        replace H : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 = x * y * z * (x + y + z):= by linarith
        trivial

      -- Series of algebraic manipulations to reach contradiction
      rw [h2] at g9
      replace g9 : x * y * z * (x + y + z) * ((x + y + z) ^ 2 - 1) > 0:= by linarith
      replace g8 : 1 > (x + y + z) ^ 2:= by
        by_contra H1
        replace H1 : (x + y + z) ^ 2 = 1:= by linarith
        rw [H1] at g9
        simp at g9
      replace g8 : (x + y + z) ^ 2 - 1 < 0:= by linarith
      replace g9 : x * y * z * (x + y + z) < 0:= by exact (neg_iff_neg_of_mul_pos g9).mpr g8

      -- Final contradiction showing this case is impossible
      by_contra H
      have g10 : x * y * z * (x + y + z) ≥ 0:= by
        have g10 : x * y * z * (x + y + z) ^ 3 ≥ 0:= by rw [←h2] ; positivity
        rw [show x * y * z * (x + y + z) ^ 3 = x * y * z * (x + y + z) * (x + y + z) ^ 2 by ring] at g10
        have g11 : (x + y + z) ^ 2 > 0:= by
          by_contra H1
          replace H1 : (x + y + z) ^ 2 ≤ 0:= by linarith
          have g11 : (x + y + z) ^ 2 ≥ 0:= by positivity
          replace g11 : (x + y + z) ^ 2 = 0:= by linarith
          replace g11 : x + y + z = 0:= by exact pow_eq_zero g11
          rw [g11] at g9
          simp at g9
        exact (mul_nonneg_iff_of_pos_right g11).mp g10
      linarith only [g9, g10]
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h | h | h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      simp
      constructor
      all_goals
        subst x y z
        simp
      .
        ring_nf
        all_goals
          norm_num
    .
      all_goals
        ring_nf
    .
      all_goals
        norm_num
