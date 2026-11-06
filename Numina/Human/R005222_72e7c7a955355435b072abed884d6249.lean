import Mathlib
set_option maxHeartbeats 400000
/- Let $a, b, c, d, e, f$ be non-negative real numbers satisfying $a+b+c+d+e+f=6$. Find the maximal possible value of

$$
a b c+b c d+c d e+d e f+e f a+f a b
$$

and determine all 6-tuples $(a, b, c, d, e, f)$ for which this maximal value is achieved.

Answer: 8 . -/
theorem algebra_606338 : IsGreatest {x | ∃ a b c d e f : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ a + b + c + d + e + f = 6 ∧ x = a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b} 8 ∧ {(a, b, c, d, e, f) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ | a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ a + b + c + d + e + f = 6 ∧ a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b = 8} = {(a, b, c, d, e, f) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 ∧ ((a, b, c, d, e, f) = (0, 0, t, 2, 2, 2 - t) ∨ (a, b, c, d, e, f) = (0, t, 2, 2, 2 - t, 0) ∨ (a, b, c, d, e, f) = (t, 2, 2, 2 - t, 0, 0) ∨ (a, b, c, d, e, f) = (2, 2, 2 - t, 0, 0, t) ∨ (a, b, c, d, e, f) = (2, 2 - t, 0, 0, t, 2) ∨ (a, b, c, d, e, f) = (2 - t, 0, 0, t, 2, 2))} := by
  -- Lemma: For non-negative real numbers x, y, z:
  -- 1. Proves that (x + y + z)^3/27 ≥ x* y* z (AM-GM inequality)
  -- 2. If equality holds, then x = y = z
  have h1 : ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → ((x + y + z)) ^ 3 / 27 ≥ x * y * z ∧ (((x + y + z) / 3) ^ 3 = x * y * z → x = y ∧ y = z):= by
    intro x y z hx hy hz
    -- First key inequality: sum of squared differences weighted by sums
    have h1 : (x + y) * (x - y) ^ 2 + (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 ≥ 0:= by positivity
    -- Second key inequality: sum of squared differences weighted by individual terms
    have h2 : z * (x - y) ^ 2 + x * (y - z) ^ 2 + y * (z - x) ^ 2 ≥ 0:= by positivity
    constructor
    .
      linarith
    .
      intro h
      -- If equality holds, then the sum of squared differences must be zero
      replace h1 : (x + y) * (x - y) ^ 2 + (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 = 0:= by linarith
      -- Each term must be non-negative
      have g1 : (x + y) * (x - y) ^ 2 ≥ 0:= by positivity
      have g2 : (y + z) * (y - z) ^ 2 ≥ 0:= by positivity
      have g3 : (z + x) * (z - x) ^ 2 ≥ 0:= by positivity
      -- Therefore each term must be zero
      replace g1 : (x + y) * (x - y) ^ 2 = 0:= by linarith
      replace g2 : (y + z) * (y - z) ^ 2 = 0:= by linarith
      replace g3 : (z + x) * (z - x) ^ 2 = 0:= by linarith
      simp at g1 g2 g3
      -- Case analysis: either x + y = 0 or x = y
      rcases g1 with g1 | g1
      .
        -- Case where x + y = 0: since x,y ≥ 0, both must be 0
        replace hx : x = 0:= by linarith
        replace hy : y = 0:= by linarith
        subst x y
        simp at g2
        subst z
        simp
      .
        -- Case where x = y: similar analysis shows y = z
        replace g1 : x = y:= by linarith
        subst x
        rcases g2 with g2 | g2
        .
          replace hy : y = z:= by linarith
          subst y
          simp
        .
          replace g2 : y = z:= by linarith
          subst y
          simp
  constructor
  .
    constructor
    .
      -- Show that 8 is achievable with specific values
      simp
      use 0
      simp
      use 0
      simp
      use 0
      simp
      use 2
      simp
      use 2
      simp
      use 2
      simp
      norm_num
    .
      -- Prove that 8 is an upper bound
      simp [upperBounds]
      intro x a ha b hb c hc d hd e he f hf h hx
      subst x
      replace h1:= (h1 (a + d) (b + e) (c + f) (by linarith) (by linarith) (by linarith)).1
      rw [show a + d + (b + e) + (c + f) = 6 by linarith] at h1
      have g1 : a * c * e ≥ 0:= by positivity
      have g2 : b * d * f ≥ 0:= by positivity
      linarith
  .
    -- Prove the equality of two sets by showing both inclusions
    ext ⟨a, b, c, d, e, f⟩
    constructor
    .
      -- Forward direction: show that any optimal solution must be in the characterized set
      intro h
      simp at h
      -- Extract all conditions from the hypothesis
      rcases h with ⟨ha, hb, hc, hd, he, hf, h3, h4⟩
      -- Apply AM-GM inequality to grouped terms (a+d), (b+e), (c+f)
      specialize h1 (a + d) (b + e) (c + f) (by linarith) (by linarith) (by linarith)
      rcases h1 with ⟨h1, h2⟩
      -- Observe that products of alternating terms must be non-negative
      have g1 : a * c * e ≥ 0:= by positivity
      have g2 : b * d * f ≥ 0:= by positivity
      -- Use the sum constraint
      have h5 : (a + d + (b + e) + (c + f)) ^ 3 = 6 ^ 3:= by rw [show a + d + (b + e) + (c + f) = 6 by linarith]
      replace h2:= h2 (by linarith)
      -- From optimality, deduce that alternating products must be zero
      replace g1 : a * c * e = 0:= by linarith
      replace g2 : b * d * f = 0:= by linarith
      clear h1 h5
      -- From equality in AM-GM, deduce relationships between paired variables
      rcases h2 with ⟨h1, h2⟩
      replace h1 : d = 2 - a:= by linarith
      replace h2 : e = 2 - b:= by linarith
      replace h3 : f = 2 - c:= by linarith
      simp
      subst d e f
      simp at g1 g2
      -- Case analysis on which terms must be zero to satisfy a* c*e = 0
      rcases g1 with g1 | g1
      .
        -- Case analysis for a* c* e = 0 and b* d*f = 0
        -- Leading to six possible configurations
        rcases g1 with g1 | g1
        .
          rcases g2 with g2 | g2
          .
            subst a
            simp at g2
            subst b
            simp at hc hf
            use c
            simp [hc, hf]
          .
            replace g2 : c = 2:= by linarith
            simp at he
            use b
            subst a c
            simp [hb, he]
        .
          subst c
          simp at g2
          rcases g2 with g2 | g2
          .
            subst b
            use (2 - a)
            simp [ha, hd]
          .
            replace g2 : a = 2:= by linarith
            subst a
            use (2 - b)
            simp [hb, he]
      .
        replace g1 : b = 2:= by linarith
        subst b
        simp at g2
        rcases g2 with g2 | g2
        .
          replace g2 : a = 2:= by linarith
          subst a
          use (2 - c)
          simp [hc, hf]
        .
          replace g2 : c = 2:= by linarith
          subst c
          use a
          simp [ha, hd]
          linarith
    .
      -- Reverse direction: verify that all characterized solutions are indeed optimal
      intro h
      simp at h
      rcases h with ⟨t, ht1, ht2, h⟩
      -- Handle all six possible configurations
      rcases h with h | h | h | h | h | h
      all_goals
        rcases h with ⟨ha, hb, hc, hd, he, hf⟩
        subst a b c d e f
        simp [ht1, ht2]
        constructor
        all_goals
          linarith
