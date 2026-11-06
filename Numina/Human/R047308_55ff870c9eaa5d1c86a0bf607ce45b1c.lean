import Mathlib
open Real
/- 9.186. $\frac{x^{3}+3 x^{2}-x-3}{x^{2}+3 x-10}<0$.

9.186. $\frac{x^{3}+3 x^{2}-x-3}{x^{2}+3 x-10}<0$. -/
theorem inequalities_171099 : {x : ℝ | (x ^ 3 + 3 * x ^ 2 - x - 3) / (x ^ 2 + 3 * x - 10) < 0} =
{x | x < -5 ∨ x ∈ Set.Ioo (-3) (-1) ∨ x ∈ Set.Ioo 1 2}:= by
  -- We use extensionality to prove equality of sets
  ext x
  simp
  -- Factor the denominator as (x - 2)(x + 5)
  rw [show x ^ 2 + 3 * x - 10 = (x - 2) * (x + 5) by ring]
  -- Factor the numerator as (x - 1)(x + 3)(x + 1)
  rw [show x ^ 3 + 3 * x ^ 2 - x - 3 = (x - 1) * (x + 3) * (x + 1) by ring]
  constructor
  .
    -- Forward direction: if the inequality holds, then x is in one of the three intervals
    intro h
    simp at h

    -- Prove that x cannot equal any of the roots of the numerator or denominator
    have h1 : x ≠ -5:= by
      by_contra
      subst x
      simp at h
    have h2 : x ≠ -3:= by
      by_contra
      subst x
      simp at h
    have h3 : x ≠ -1:= by
      by_contra
      subst x
      simp at h
    have h4 : x ≠ 1:= by
      by_contra
      subst x
      simp at h
    have h5 : x ≠ 2:= by
      by_contra
      subst x
      simp at h
    -- Show that the square of the denominator is positive
    have g1 : (x - 2) ^ 2 * (x + 5) ^ 2 > 0:= by
      replace h5 : x - 2 ≠ 0:= by
        by_contra H
        replace H : x = 2:= by linarith
        trivial
      replace h1 : x + 5 ≠ 0:= by
        by_contra H
        replace H : x = -5:= by linarith
        trivial
      positivity
    -- Show that the denominator is non-zero
    have g2 : (x - 2) * (x + 5) ≠ 0:= by
      by_contra H
      simp at H
      rcases H with H | H
      .
        replace H : x = 2:= by linarith
        trivial
      .
        replace H : x = -5:= by linarith
        trivial
    -- Manipulate the inequality to eliminate the division
    replace h : -((x - 1) * (x + 3) * (x + 1) / ((x - 2) * (x + 5))) > 0:= by linarith
    replace h : -((x - 1) * (x + 3) * (x + 1) / ((x - 2) * (x + 5))) * ((x - 2) ^ 2 * (x + 5) ^ 2) > 0:= by positivity
    rw [show -((x - 1) * (x + 3) * (x + 1) / ((x - 2) * (x + 5))) * ((x - 2) ^ 2 * (x + 5) ^ 2) = -((x - 2) * (x - 1) * (x + 3) * (x + 1) * (x + 5)) by field_simp ; linarith] at h
    clear g1 g2
    -- Determine which interval x belongs to by analyzing the signs of factors
    apply lt_or_gt_of_ne at h1
    apply lt_or_gt_of_ne at h2
    apply lt_or_gt_of_ne at h3
    apply lt_or_gt_of_ne at h4
    apply lt_or_gt_of_ne at h5
    rcases h1 with h1 | h1
    .
      -- Case: x < -5
      left
      exact h1
    .
      rcases h2 with h2 | h2
      .
        -- Case: -5 < x < -3 (contradiction)
        have g1 : x + 5 > 0:= by linarith
        have g2 : -(x - 2) > 0:= by linarith
        have g3 : -(x + 3) > 0:= by linarith
        have g4 : -(x - 1) > 0:= by linarith
        have g5 : -(x + 1) > 0:= by linarith
        have g6 : (x + 5) * (-(x - 2)) * (-(x + 3)) * (-(x - 1)) * (-(x + 1)) > 0:= by positivity
        linarith
      .
        clear h1
        rcases h3 with h3 | h3
        .
          -- Case: -3 < x < -1
          right
          left
          exact ⟨h2, h3⟩
        .
          clear h2
          rcases h4 with h4 | h4
          .
            -- Case: -1 < x < 1 (contradiction)
            have g1 : x + 5 > 0:= by linarith
            have g2 : -(x - 2) > 0:= by linarith
            have g3 : x + 3 > 0:= by linarith
            have g4 : -(x - 1) > 0:= by linarith
            have g5 : x + 1 > 0:= by linarith
            have g6 : (x + 5) * (-(x - 2)) * (x + 3) * (-(x - 1)) * (x + 1) > 0:= by positivity
            linarith
          .
            clear h3
            rcases h5 with h5 | h5
            .
              -- Case: 1 < x < 2
              right
              right
              exact ⟨h4, h5⟩
            .
              -- Case: x > 2 (contradiction)
              clear h4
              have g2 : x - 2 > 0:= by linarith
              have g4 : x - 1 > 0:= by linarith
              have g6 : (x + 5) * (x - 2) * (x + 3) * (x - 1) * (x + 1) > 0:= by positivity
              linarith
  .
    -- Backward direction: if x is in one of the three intervals, then the inequality holds
    intro h
    rcases h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    .
      -- Case: x < -5
      have g1 : x - 2 < 0:= by linarith
      have g2 : x + 5 < 0:= by linarith
      have g3 : x - 1 < 0:= by linarith
      have g4 : x + 3 < 0:= by linarith
      have g5 : x + 1 < 0:= by linarith
      have g6:= mul_pos_of_neg_of_neg g1 g2
      have g7:= mul_pos_of_neg_of_neg g3 g4
      replace g7:= mul_neg_of_pos_of_neg g7 g5
      exact div_neg_of_neg_of_pos g7 g6
    .
      -- Case: -3 < x < -1
      have g1 : x - 2 < 0:= by linarith
      have g2 : x + 5 > 0:= by linarith
      have g3 : x - 1 < 0:= by linarith
      have g4 : x + 3 > 0:= by linarith
      have g5 : x + 1 < 0:= by linarith
      have g6:= mul_neg_of_neg_of_pos g1 g2
      have g7:= mul_neg_of_neg_of_pos g3 g4
      replace g7:= mul_pos_of_neg_of_neg g7 g5
      exact div_neg_of_pos_of_neg g7 g6
    .
      -- Case: 1 < x < 2
      have g1 : x - 2 < 0:= by linarith
      have g2 : x + 5 > 0:= by linarith
      have g3 : x - 1 > 0:= by linarith
      have g4 : x + 3 > 0:= by linarith
      have g5 : x + 1 > 0:= by linarith
      have g6:= mul_neg_of_neg_of_pos g1 g2
      have g7:= mul_pos g3 g4
      replace g7:= mul_pos g7 g5
      exact div_neg_of_pos_of_neg g7 g6
