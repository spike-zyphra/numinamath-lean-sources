import Mathlib
/- Example 1 (2001 Austrian-Polish Mathematical Olympiad Problem) Given that $a, b, c$ are the three sides of $\triangle ABC$, prove: $2<$ $\frac{b+c}{a}+\frac{c+a}{b}+\frac{a+b}{c}-\frac{a^{3}+b^{3}+c^{3}}{a b c} \leqslant 3$. -/
theorem inequalities_600041 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b): 2 < (b + c) / a + (c + a) / b + (a + b) / c - (a^3 + b^3 + c^3) / (a * b * c) ∧ (b + c) / a + (c + a) / b + (a + b) / c - (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) ≤ 3:= by
  -- Establish that the product of the sides is positive
  have g1 : a * b * c > 0:= by positivity
  -- Split the proof into two parts: lower bound and upper bound
  constructor
  -- First part: proving the lower bound (> 2)
  .
    -- Simplify the expression by clearing denominators
    field_simp
    -- Convert the inequality to a form with common denominator
    suffices 2 * (a * b * c) < (((b + c) * b + (c + a) * a) * c + (a + b) * (a * b) - (a ^ 3 + b ^ 3 + c ^ 3)) by exact(lt_div_iff₀ g1).mpr this
    -- Rewrite the triangle inequalities in a more useful form
    replace h1 : b + c - a > 0:= by linarith
    replace h2 : c + a - b > 0:= by linarith
    replace h3 : a + b - c > 0:= by linarith
    -- Show that the product of these differences is positive
    have g2 : (b + c - a) * (c + a - b) * (a + b - c) > 0:= by positivity
    -- Complete the proof of the lower bound using linear arithmetic
    linarith
  -- Second part: proving the upper bound (≤ 3)
  .
    -- Simplify the expression by clearing denominators
    field_simp
    -- Convert the inequality to a form with common denominator
    suffices (((b + c) * b + (c + a) * a) * c + (a + b) * (a * b) - (a ^ 3 + b ^ 3 + c ^ 3)) ≤ 3 * (a * b * c) by exact(div_le_iff₀ g1).mpr this
    -- Consider all possible orderings of a, b, and c
    have h4 : (a ≥ b ∧ b ≥ c) ∨ (a ≥ c ∧ c ≥ b) ∨ (b ≥ a ∧ a ≥ c) ∨ (b ≥ c ∧ c ≥ a) ∨ (c ≥ a ∧ a ≥ b) ∨ (c ≥ b ∧ b ≥ a):= by
      -- Clear unnecessary hypotheses for this part
      clear ha hb hc h1 h2 h3 g1
      -- Case analysis on the ordering of a and b
      by_cases h1 : a ≥ b
      .
        -- If a ≥ b, consider the ordering of b and c
        by_cases h2 : b ≥ c
        .
          tauto
        .
          simp at h2
          replace h2 : b ≤ c:= by linarith
          -- Consider the ordering of c and a
          by_cases h3 : c ≥ a
          .
            tauto
          .
            simp at h3
            replace h3 : c ≤ a:= by linarith
            tauto
      .
        -- If a < b, consider other orderings
        simp at h1
        replace h1 : a ≤ b:= by linarith
        by_cases h2 : b ≤ c
        .
          tauto
        .
          simp at h2
          replace h2 : b ≥ c:= by linarith
          by_cases h3 : c ≥ a
          .
            tauto
          .
            simp at h3
            replace h3 : c ≤ a:= by linarith
            tauto
    -- Establish a key inequality for the upper bound proof
    have h5 : ∀ a b c : ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → a ≥ b → b ≥ c → a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) ≥ 0:= by
      intro a b c ha _ hc h1 h2
      -- Show that one term is non-negative
      have g1 : c * (a - c) * (b - c) ≥ 0:= by
        have g1 : a - c ≥ 0:= by linarith
        have g2 : b - c ≥ 0:= by linarith
        positivity
      -- Establish additional inequalities needed for the proof
      have g2 : a - c ≥ b - c:= by linarith
      replace h1 : a - b ≥ 0:= by linarith
      replace g2:= mul_le_mul_of_nonneg_left g2 h1
      replace g2:= mul_le_mul_of_nonneg_left g2 ha
      replace h2 : b - c ≥ 0:= by linarith
      replace h2 : (a - b) ^ 2 * (b - c) ≥ 0:= by positivity
      linarith
    -- Handle all six possible orderings of a, b, c
    rcases h4 with h4 | h4 | h4 | h4 | h4 | h4
    all_goals
      rcases h4 with ⟨h41, h42⟩
    -- Case 1: a ≥ b ≥ c
    .
      linarith only [h5 a b c (by linarith) (by linarith) (by linarith) h41 h42]
    -- Case 2: a ≥ c ≥ b
    .
      linarith only [h5 a c b (by linarith) (by linarith) (by linarith) h41 h42]
    -- Case 3: b ≥ a ≥ c
    .
      linarith only [h5 b a c (by linarith) (by linarith) (by linarith) h41 h42]
    -- Case 4: b ≥ c ≥ a
    .
      linarith only [h5 b c a (by linarith) (by linarith) (by linarith) h41 h42]
    -- Case 5: c ≥ a ≥ b
    .
      linarith only [h5 c a b (by linarith) (by linarith) (by linarith) h41 h42]
    -- Case 6: c ≥ b ≥ a
    .
      linarith only [h5 c b a (by linarith) (by linarith) (by linarith) h41 h42]
