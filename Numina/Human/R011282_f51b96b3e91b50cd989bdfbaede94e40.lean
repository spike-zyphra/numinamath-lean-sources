import Mathlib
/- 26. (VIE 2) Let $a, b, c, d$ be four nonnegative numbers satisfying $a+b+c+d=$ 1. Prove the inequality  $$ a b c+b c d+c d a+d a b \leq \frac{1}{27}+\frac{176}{27} a b c d $$ -/
theorem inequalities_24502 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
a * b * c + b * c * d + c * d * a + d * a * b ≤ 1 / 27 + 176 / 27 * a * b * c * d:= by
  -- Rearranging the inequality to a more convenient form
  suffices a * b * (c + d) + c * d * (a + b - 176 / 27 * a * b) ≤ 1 / 27 by linarith

  -- Helper lemma: For nonnegative x, y, z, we have x*y*z ≤ (x+y+z)³/27
  have h3 : ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x * y * z ≤ (x + y + z) ^ 3 / 27:= by
    intro x y z hx hy hz
    -- These inequalities help establish the AM-GM inequality
    have g1 : (x + y) * (x - y) ^ 2 + (x + z) * (x - z) ^ 2 + (y + z) * (y - z) ^ 2 ≥ 0:= by positivity
    have g2 : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≥ 0:= by positivity
    linarith

  -- Split into two cases based on the sign of (a + b - 176/27 * a * b)
  by_cases h1 : a + b - 176 / 27 * a * b ≤ 0
  .
    -- Case 1: When a + b - 176/27 * a * b ≤ 0
    have h2 : c * d ≥ 0:= by positivity
    replace h1 : c * d * (a + b - 176 / 27 * a * b) ≤ 0:= by exact mul_nonpos_of_nonneg_of_nonpos h2 h1
    specialize h3 a b (c + d) ha hb (by linarith)
    rw [show a + b + (c + d) = 1 by linarith] at h3
    linarith
  .
    -- Case 2: When a + b - 176/27 * a * b > 0
    push_neg at h1

    -- Using the inequality c*d ≤ (c+d)²/4
    have g1 : c * d * (a + b - 176 / 27 * a * b) ≤ (c + d) ^ 2 * (a + b - 176 / 27 * a * b) / 4:= by
      suffices (c - d) ^ 2 * (a + b - 176 / 27 * a * b) ≥ 0 by linarith
      positivity

    -- Simplifying the inequality further
    suffices 4 * a * b * (c + d) + (c + d) ^ 2 * (a + b - 176 / 27 * a * b) ≤ 4 / 27 by linarith
    clear g1

    -- Substituting c + d = 1 - (a + b) and introducing variables t and s
    rw [show c + d = 1 - (a + b) by linarith]
    set t:= a + b with ht
    set s:= a * b with hs
    clear_value t s

    -- Rewriting in terms of t and s
    rw [show 176 / 27 * a * b = 176 / 27 * s by subst s ; ring] at h1 ⊢
    replace h : t ≤ 1:= by linarith
    have h2 : t ≥ 0:= by linarith
    replace h1 : t > 176 / 27 * s:= by linarith
    rw [show 4 * a * b = 4 * s by subst s ; ring]

    -- Algebraic manipulation to simplify the expression
    rw [show 4 * s * (1 - t) + (1 - t) ^ 2 * (t - 176 / 27 * s) = t * (1 - t) ^ 2 + 4 / 27 * (1 - t) * (44 * t - 17) * s by ring_nf]

    -- Further case analysis based on the sign of (44*t - 17)
    by_cases g3 : 44 * t - 17 ≤ 0
    .
      -- Subcase 2.1: When 44*t - 17 ≤ 0
      replace g3 : 17 - 44 * t ≥ 0:= by linarith
      have g1 : 1 - t ≥ 0:= by linarith
      have g2 : s ≥ 0:= by subst s ; positivity
      replace g3 : (1 - t) * (17 - 44 * t) * s ≥ 0:= by positivity
      suffices t * (1 - t) ^ 2 ≤ 4 / 27 by linarith

      -- Applying the AM-GM inequality
      specialize h3 (2 * t) (1 - t) (1 - t) (by linarith) (by linarith) (by linarith)
      rw [show 2 * t + (1 - t) + (1 - t) = 2 by ring] at h3
      linarith
    .
      -- Subcase 2.2: When 44*t - 17 > 0
      simp at g3
      replace g3 : 44 * t - 17 > 0:= by linarith

      -- Further splitting based on whether t ≥ 27/44
      by_cases ht1 : t ≥ 27 / 44
      .
        -- Subcase 2.2.1: When t ≥ 27/44
        have g4 : 4 / 27 * (1 - t) * (44 * t - 17) * s ≤ 1 / 44 * (1 - t) * (44 * t - 17) * t:= by
          have g4 : (1 - t) * (44 * t - 17) ≥ 0:= by
            replace h : 1 - t ≥ 0:= by linarith
            positivity
          suffices (1 - t) * (44 * t - 17) * (t - 176 / 27 * s) ≥ 0 by linarith
          replace h1 : t - 176 / 27 * s ≥ 0:= by linarith
          positivity

        -- Final step for this subcase using non-linear arithmetic
        suffices (27 / 44 * t * (1 - t) ≤ 4 / 27) by linarith
        nlinarith only [ht1]
      .
        -- Subcase 2.2.2: When t < 27/44
        simp at ht1

        -- Using the inequality s ≤ t²/4
        have g4 : 4 / 27 * (1 - t) * (44 * t - 17) * s ≤ 1 / 27 * (1 - t) * (44 * t - 17) * t ^ 2:= by
          have g4 : (1 - t) * (44 * t - 17) ≥ 0:= by
            replace h : 1 - t ≥ 0:= by linarith
            positivity
          suffices (1 - t) * (44 * t - 17) * (t ^ 2 - 4 * s) ≥ 0 by linarith
          have g5 : t ^ 2 - 4 * s ≥ 0:= by
            subst t s
            suffices (a - b) ^ 2 ≥ 0 by linarith
            positivity
          positivity

        -- Final steps using algebraic manipulation and non-linear arithmetic
        suffices t * (1 - t) ^ 2 + 1 / 27 * (1 - t) * (44 * t - 17) * t ^ 2 ≤ 4 / 27 by linarith
        suffices (t * (1 - t)) * (27 / 44 - t * (1 - t)) ≤ 1 / 11 by linarith
        set A:= t * (1 - t) with hA
        clear_value A

        -- Using the fact that t*(1-t) ≤ 1/4
        have hA1 : A ≤ 1 / 4:= by
          subst A
          suffices (t - 1 / 2) ^ 2 ≥ 0 by linarith
          positivity
        nlinarith only [hA1]
