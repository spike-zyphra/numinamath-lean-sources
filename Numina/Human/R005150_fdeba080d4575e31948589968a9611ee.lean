import Mathlib
/- Vind alle functies $f: \mathbb{R}_{\geq 0} \rightarrow \mathbb{R}$ die voldoen aan

$$
2 x^{3} z f(z)+y f(y) \geq 3 y z^{2} f(x)
$$

voor alle $x, y, z \in \mathbb{R}_{\geq 0}$. -/
theorem algebra_605836 (f : ℝ → ℝ) : (∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → 2 * x ^ 3 * z * f z + y * f y ≥ 3 * y * z ^ 2 * f x) ↔ (f 0 ≤ 0 ∧ ∃ c : ℝ, c ≥ 0 ∧ ∀ x : ℝ, x > 0 → f x = c * x ^ 2):= by
  constructor
  -- Forward direction: proving that any function satisfying the inequality must have the specified form
  .
    intro h
    -- First prove that f(0) ≤ 0 by contradiction
    have h0 : f 0 ≤ 0:= by
      by_contra H
      simp at H
      have h1 : ∀ z : ℝ, z ≥ 0 → f 1 ≥ 3 * f 0 * z ^ 2:= by
        intro z hz
        specialize h 0 1 z (by linarith) (by linarith) (by linarith)
        simp at h
        linarith
      specialize h1 |√((|f 1| + 1) / (3 * f 0))| (by positivity)
      rw [sq_abs √((|f 1| + 1) / (3 * f 0))] at h1
      rw [show √((|f 1| + 1) / (3 * f 0)) ^ 2 = (|f 1| + 1) / (3 * f 0) by refine Real.sq_sqrt (by positivity)] at h1
      rw [show 3 * f 0 * ((|f 1| + 1) / (3 * f 0)) = |f 1| + 1 by field_simp] at h1
      have h2 : |f 1| ≥ f 1:= by exact le_abs_self (f 1)
      linarith
    -- Prove that f(y) ≥ 0 for all y > 0
    have h1 : ∀ y : ℝ, y > 0 → f y ≥ 0:= by
      intro y hy
      specialize h 0 y 0 (by linarith) (by linarith) (by linarith)
      simp at h
      exact nonneg_of_mul_nonneg_right h hy
    -- Prove upper bound: f(y) ≤ y²f(1) for all y > 0
    have h2 : ∀ y : ℝ, y > 0 → f y ≤ y ^ 2 * f 1:= by
      intro y hy
      specialize h y y 1 (by linarith) (by linarith) (by linarith)
      simp at h
      replace h : y * f y ≤ y * (y ^ 2 * f 1):= by linarith
      exact le_of_mul_le_mul_left h hy
    -- Prove lower bound: f(y) ≥ y²f(1) for all y > 0
    have h3 : ∀ y : ℝ, y > 0 → f y ≥ y ^ 2 * f 1:= by
      intro y hy
      specialize h 1 y y (by linarith) (by linarith) (by linarith)
      simp at h
      replace h : y * f y ≥ y * (y ^ 2 * f 1):= by linarith
      exact le_of_mul_le_mul_left h hy
    constructor
    .
      exact h0
    -- Show that f(x) = cx² for some c ≥ 0 when x > 0
    .
      use (f 1)
      constructor
      .
        exact (h1 1 (by linarith))
      .
        intro y hy
        specialize h2 y hy
        specialize h3 y hy
        linarith
  -- Reverse direction: proving that a function of the specified form satisfies the inequality
  .
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h2 with ⟨c, hc, h3⟩
    intro x y z hx hy hz
    -- Case analysis on x = 0
    by_cases gx : x = 0
    .
      subst x
      simp
      by_cases gy : y = 0
      .
        subst y
        simp
      .
        replace hy : y > 0:= by positivity
        rw [h3 y hy]
        replace h1 : -f 0 ≥ 0:= by linarith
        have g1 : 3 * y * z ^ 2 * (-f 0) ≥ 0:= by positivity
        have g2 : y * (c * y ^ 2) ≥ 0:= by positivity
        linarith
    .
      replace hx : x > 0:= by positivity
      clear gx
      -- Case analysis on y = 0
      by_cases gy : y = 0
      .
        subst y
        simp
        by_cases gz : z = 0
        .
          subst z
          simp
        .
          replace hz : z > 0:= by positivity
          rw [h3 z hz]
          positivity
      .
        replace hy : y > 0:= by positivity
        clear gy
        by_cases gz : z = 0
        .
          subst z
          simp
          rw [h3 y hy]
          positivity
        .
          replace hz : z > 0:= by positivity
          clear gz
          rw [h3 x hx, h3 y hy, h3 z hz]
          ring_nf
          suffices c * (2 * x ^ 3 * z ^ 3 + y ^ 3) ≥ c * (3 * y * z ^ 2 * x ^ 2) by linarith
          by_cases hc1 : c = 0
          .
            subst c
            simp
          .
            replace hc1 : c > 0:= by positivity
            suffices (2 * x ^ 3 * z ^ 3 + y ^ 3) ≥ (3 * y * z ^ 2 * x ^ 2) by exact (mul_le_mul_iff_of_pos_left hc1).mpr this
            have g1 : ∀ a b c : ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 0:= by
              intro a b c ha hb hc
              have g1 : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0:= by positivity
              linarith
            specialize g1 (x * z) (x * z) y (by positivity) (by positivity) (by positivity)
            linarith
