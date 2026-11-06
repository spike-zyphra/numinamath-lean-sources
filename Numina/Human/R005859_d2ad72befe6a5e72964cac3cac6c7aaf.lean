import Mathlib
/- Let $a$ and $b$ be positive integers with $a>b$. Suppose that

$$
\sqrt{\sqrt{a}+\sqrt{b}}+\sqrt{\sqrt{a}-\sqrt{b}}
$$

is a integer.
(a) Must $\sqrt{a}$ be an integer?
(b) Must $\sqrt{b}$ be an integer? -/
theorem algebra_610324 : (∀ a b : ℤ, a > 0 → b > 0 → a > b → (∃ k : ℤ, √(√a + √b) + √(√a - √b) = k) → ∃ t : ℤ, √a = t) ∧ (∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a > b ∧ (∃ k : ℤ, √(√a + √b) + √(√a - √b) = k) ∧ (∀ t : ℤ, √b ≠ t)):= by
  constructor
  -- Part (a): Proving that √a must be an integer
  .
    intro a b ha hb hab h
    rcases h with ⟨k, hk⟩
    -- Rearranging the equation to isolate each square root
    have h1 : √(√↑a + √↑b) = ↑k - √(√↑a - √↑b):= by linarith
    have h2 : √(√↑a - √↑b) = ↑k - √(√↑a + √↑b):= by linarith
    -- Squaring both sides of the equations
    replace h1 : (√(√↑a + √↑b)) ^ 2  = (↑k - √(√↑a - √↑b)) ^ 2:= by rw [h1]
    replace h2 : (√(√↑a - √↑b)) ^ 2  = (↑k - √(√↑a + √↑b)) ^ 2:= by rw [h2]
    -- Establishing that both expressions under the square roots are positive
    have g1 : √a + √b > 0:= by positivity
    have g2 : √a > √b:= by
      rify at hab hb
      replace hb : (↑b : ℝ) ≥ 0:= by linarith
      exact Real.sqrt_lt_sqrt hb hab
    replace g2 : √a - √b > 0:= by linarith
    -- Simplifying the squared equations
    field_simp at h1 h2
    ring_nf at h1 h2
    field_simp at h1 h2
    -- Further manipulating the equations
    replace h1 : ↑k * √(√↑a - √↑b) * 2 = k ^ 2 - 2 * √b:= by linarith
    replace h2 : ↑k * √(√↑a + √↑b) * 2 = k ^ 2 + 2 * √b:= by linarith
    -- Squaring again to eliminate remaining square roots
    replace h1 : (↑k * √(√↑a - √↑b) * 2) ^ 2 = (k ^ 2 - 2 * √b) ^ 2:= by rw [h1]
    replace h2 : (↑k * √(√↑a + √↑b) * 2) ^ 2 = (k ^ 2 + 2 * √b) ^ 2:= by rw [h2]
    ring_nf at h1 h2
    field_simp at h1 h2
    -- Key equation relating √a to k and b
    have h3 : 4 * k ^ 2 * √a = k ^ 4 + 4 * b:= by linarith
    -- Proving k is non-zero
    have h4 : k ≠ 0:= by
      by_contra H
      subst k
      have h5 : √(√↑a + √↑b) + √(√↑a - √↑b) > 0:= by positivity
      simp at hk
      linarith
    clear hb hab g1 g2 h1 h2 hk
    -- Helper lemma: if √a is rational, then it's an integer
    have h1 : (∃ r : ℚ, √a = r) → ∃ t : ℤ, √a = t:= by
      intro h
      rcases h with ⟨r, hr⟩
      have h2:= Rat.mul_self_den r
      have h:= hr
      replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
      field_simp at hr
      replace hr : a = r ^ 2:= by rify ; linarith
      have g2 : (↑a : ℚ).den = 1:= by exact rfl
      rw [show r * r = r ^ 2 by ring_nf] at h2
      rw [hr, h2] at g2
      simp at g2
      rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
      rw [g2] at h
      simp at h
      use r.num
    -- Expressing √a as a rational number
    replace h3 : √a = (k ^ 4 + 4 * b) / (4 * k ^ 2):= by
      field_simp
      linarith
    replace h3 : ∃ r : ℚ, √a = r:= by
      use (k ^ 4 + 4 * b) / (4 * k ^ 2)
      rify
      exact h3
    exact h1 h3
  -- Part (b): Providing a counterexample where √b is not an integer
  .
    -- Using a = 36 and b = 32 as a counterexample
    use 36, 32
    simp
    constructor
    -- Proving that a > 0, b > 0, a > b, and √(√a + √b) + √(√a - √b) = 4
    .
      use 4
      rw [show √36 = √(6 ^ 2) by ring_nf]
      rw [show √32 = √(4 ^ 2 * 2) by ring_nf]
      field_simp
      -- Simplifying the expressions under the square roots
      rw [show 6 + 4 * √2 = (2 + √2) ^ 2 by ring_nf ; field_simp ; linarith]
      rw [show 6 - 4 * √2 = (2 - √2) ^ 2 by ring_nf ; field_simp ; linarith]
      -- Proving that 2 - √2 > 0
      have g1 : √(2 ^ 2) > √2:= by
        have g2 : (2 : ℝ) ^ 2 > 2:= by linarith
        have g3 : (2 : ℝ) ≥ 0:= by linarith
        exact Real.sqrt_lt_sqrt g3 g2
      field_simp at g1
      replace g1 : 2 - √2 > 0:= by linarith
      field_simp
      linarith
    -- Proving that √b = √32 = 4√2 is not an integer
    .
      by_contra H
      simp at H
      rcases H with ⟨t, ht⟩
      -- If √b = t for some integer t, then t must be positive
      have hpos : t > 0:= by rify ; rw [←ht] ; positivity
      -- Proving that t > 5
      have h1 : t > 5:= by
        by_contra H
        simp at H
        replace H : t ^ 2 ≤ 25:= by nlinarith only [hpos, H]
        rify at H
        rw [←ht] at H
        field_simp at H
        linarith
      -- Proving that t < 6
      have h2 : t < 6:= by
        by_contra H
        simp at H
        replace H : 36 ≤ t ^ 2:= by nlinarith only [hpos, H]
        rify at H
        rw [←ht] at H
        field_simp at H
        linarith
      -- Contradiction: t cannot be both > 5 and < 6 as an integer
      linarith
