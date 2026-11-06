import Mathlib

open Real Set
open scoped BigOperators

/- The graphs of $y=|x|$ and $y=-x^2-3x-2$ are drawn.  For every $x$, a vertical segment connecting these two graphs can be drawn as well.  Find the smallest possible length of one of these vertical segments. -/
theorem algebra_10694 :
  IsLeast {(y : ℝ) | ∃ x, y = |(|x| - (-x^2 - 3*x - 2))|} 1 := by
  dsimp
  constructor
  -- Proof that 1 belongs to the set
  . simp_all
    -- We show that when x = -1, the expression evaluates to 1
    have h1 : (1 : ℝ) = |(|-1| - (-(-1) ^ 2 - 3 * (-1) - 2))| := by norm_num
    -- Existential introduction with witness -1 and proof h1
    exact ⟨-1, h1⟩
  -- Proof that for all y in the set, y >= 1
  . rintro y hy
    dsimp at hy
    obtain ⟨x, hx⟩ := hy
    -- Case analysis on whether x < 0 or not
    by_cases h₁ : x < 0
    -- Case x < 0
    . -- When x is negative, |x| = -x
      have : |x| = -x := by
        simp [abs_of_neg]
        exact h₁.le
      rw [this] at hx
      -- Show that y can be rewritten as (x + 1)^2 + 1
      have : y = (x + 1)^2 + 1 := by
        calc
        y = |-x - (-x ^ 2 - 3 * x - 2)| := by simp [hx]
        _ = |(x + 1)^2 + 1| := by ring_nf
        _ = (x + 1)^2 + 1 := by norm_num; nlinarith
      nlinarith
    -- Case 0 ≤ x
    . -- When x is non-negative, |x| = x
      simp_all
      have : |x| = x := by simp [abs_of_nonneg h₁]
      rw [this]
      have : 2 ≤ (x + 2)^2 - 2 := by nlinarith
      have : |x - (-x ^ 2 - 3 * x - 2)| = (x + 2)^2 - 2 := by
        calc
        |x - (-x ^ 2 - 3 * x - 2)| = |(x + 2)^2 - 2| := by ring_nf
                                 _ = (x + 2)^2 - 2 := by simp [abs_of_nonneg]; nlinarith
      -- Substitute the expression for y and conclude that y >= 1
      rw [this]
      nlinarith
