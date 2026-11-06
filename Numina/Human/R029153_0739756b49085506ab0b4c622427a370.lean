import Mathlib
/- 79. Let $a, b, c \geq 0, a+b+c=2$, prove:
$$\frac{a b}{1+c^{2}}+\frac{b c}{1+a^{2}}+\frac{c a}{1+b^{2}} \leq 1 \quad \text { (Pham Kim Hung) }$$ -/
theorem inequalities_597888 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 2) :
a * b / (1 + c ^ 2) + b * c / (1 + a ^ 2) + c * a / (1 + b ^ 2) ≤ 1:= by
  -- Establish that denominators are positive
  have g1 : 1 + a ^ 2 > 0:= by positivity
  have g2 : 1 + b ^ 2 > 0:= by positivity
  have g3 : 1 + c ^ 2 > 0:= by positivity
  have g4 : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) > 0:= by positivity

  -- Multiply both sides by the product of denominators to clear fractions
  suffices (a * b / (1 + c ^ 2) + b * c / (1 + a ^ 2) + c * a / (1 + b ^ 2)) * ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≤ 1 * ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) by exact le_of_mul_le_mul_right this g4

  -- Simplify the left side of the inequality using field operations
  rw [show (a * b / (1 + c ^ 2) + b * c / (1 + a ^ 2) + c * a / (1 + b ^ 2)) * ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) = a * b * (1 + a ^ 2) * (1 + b ^ 2) + b * c * (1 + b ^ 2) * (1 + c ^ 2) + c * a * (1 + c ^ 2) * (1 + a ^ 2) by field_simp ; linarith]

  -- Define x as the sum of products of pairs
  set x:= a * b + b * c + c * a with hx
  clear_value x

  -- Establish that the square of products of differences is non-negative
  have h1 : (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0:= by positivity

  -- Prove a key inequality for ordered triples
  have h2 : ∀ a b c : ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → a ≥ b → b ≥ c → a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) ≥ 0:= by
    intro a b c ha hb _ h1 h2
    -- Show that the third term is non-negative
    have g1 : c ^ 2 * (c - a) * (c - b) ≥ 0:= by
      have g1 : a - c ≥ 0:= by linarith
      have g2 : b - c ≥ 0:= by linarith
      have g3 : c ^ 2 * (a - c) * (b - c) ≥ 0:= by positivity
      linarith

    -- Compare products of differences
    have g2 : (a - b) * (a - c) ≥ (a - b) * (b - c):= by
      have g1 : a - b ≥ 0:= by linarith
      have g2 : a - c ≥ b - c:= by linarith
      exact mul_le_mul_of_nonneg_left g2 g1

    -- Show that a² ≥ b²
    have g3 : a ^ 2 ≥ b ^ 2:= by
      have g1 : a - b ≥ 0:= by linarith
      replace g1 : (a + b) * (a - b) ≥ 0:= by positivity
      linarith

    -- Show that (a-b)(b-c) ≥ 0
    have g4 : (a - b) * (b - c) ≥ 0:= by
      have g1 : a - b ≥ 0:= by linarith
      have g2 : b - c ≥ 0:= by linarith
      positivity

    -- Combine the inequalities
    replace g2 : a ^ 2 * ((a - b) * (a - c)) ≥ b ^ 2 * ((a - b) * (b - c)):= by refine mul_le_mul g3 g2 g4 (by positivity)
    linarith

  -- Apply the key inequality to our specific case
  replace h2 : a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) ≥ 0:= by
    -- Consider all possible orderings of a, b, c
    have h3 : (a ≥ b ∧ b ≥ c) ∨ (a ≥ c ∧ c ≥ b) ∨ (b ≥ a ∧ a ≥ c) ∨ (b ≥ c ∧ c ≥ a) ∨ (c ≥ a ∧ a ≥ b) ∨ (c ≥ b ∧ b ≥ a):= by
      by_cases h1 : a ≥ b
      .
        by_cases h2 : b ≥ c
        .
          tauto
        .
          simp at h2
          replace h2 : b ≤ c:= by linarith
          by_cases h3 : c ≥ a
          .
            tauto
          .
            simp at h3
            replace h3 : c ≤ a:= by linarith
            tauto
      .
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

    -- Apply the key inequality to each possible ordering
    rcases h3 with h3 | h3 | h3 | h3 | h3 | h3
    all_goals
      rcases h3 with ⟨h3, h4⟩
    .
      linarith only [h2 a b c ha hb hc h3 h4]
    .
      linarith only [h2 a c b ha hc hb h3 h4]
    .
      linarith only [h2 b a c hb ha hc h3 h4]
    .
      linarith only [h2 b c a hb hc ha h3 h4]
    .
      linarith only [h2 c a b hc ha hb h3 h4]
    .
      linarith only [h2 c b a hc hb ha h3 h4]

  -- Define auxiliary expressions A and B
  set A:= (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 with hA
  set B:= a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) with hB
  clear_value A B
  simp

  -- Reformulate the goal in terms of non-negativity
  suffices (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) - (a * b * (1 + a ^ 2) * (1 + b ^ 2) + b * c * (1 + b ^ 2) * (1 + c ^ 2) + c * a * (1 + c ^ 2) * (1 + a ^ 2)) ≥ 0 by linarith only [this]

  -- Express the difference in terms of A, B, and x
  have h3 : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) - (a * b * (1 + a ^ 2) * (1 + b ^ 2) + b * c * (1 + b ^ 2) * (1 + c ^ 2) + c * a * (1 + c ^ 2) * (1 + a ^ 2)) = (6 * A + 5 / 2 * (1 + 9 * x) * B + (1 - x) ^ 2 * (365 - 147 * x)) / 81:= by
    subst x A B
    replace h : a = 2 - b - c:= by linarith
    subst a
    ring_nf
  rw [h3]
  clear h3 hA hB g1 g2 g3 g4

  -- Show that x is non-negative
  have h3 : x ≥ 0:= by subst x ; positivity

  -- Show that 365 - 147*x ≥ 0
  have h4 : 365 - 147 * x ≥ 0:= by
    have h4 : x ≤ 2 ^ 2 / 3:= by
      rw [←h]
      subst x
      suffices (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 by linarith only [this]
      positivity
    linarith only [h4]

  -- Complete the proof by showing the expression is non-negative
  positivity
