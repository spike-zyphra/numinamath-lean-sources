import Mathlib
/- 9.172 Let $a, b, c$ be positive real numbers, and satisfy $abc=1$. Prove:
$$\frac{ab}{a^{5}+b^{5}+ab}+\frac{bc}{b^{5}+c^{5}+bc}+\frac{ca}{c^{5}+a^{5}+ca} \leqslant 1,$$

and specify when equality holds. -/
theorem inequalities_602032 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 ∧
(a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) = 1 ↔
(a = 1 ∧ b = 1 ∧ c = 1)):= by
  -- Key inequality: For positive x and y, x^5 + y^5 + xy ≥ x^2*y^2*(x+y) + xy
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x ^ 5 + y ^ 5 + x * y ≥ x ^ 2 * y ^ 2 * (x + y) + x * y:= by
    intro x y hx hy
    -- This is proven by showing that (x+y)(x^2+xy+y^2)(x-y)^2 ≥ 0
    have h1 : (x + y) * (x ^ 2 + x * y + y ^ 2) * (x - y) ^ 2 ≥ 0:= by positivity
    linarith

  -- Apply the key inequality to each pair of variables
  have h2:= h1 c a hc ha
  have h3:= h1 a b ha hb
  replace h1:= h1 b c hb hc

  -- Establish that products are non-negative
  have g1 : b * c ≥ 0:= by positivity
  have g2 : c * a ≥ 0:= by positivity
  have g3 : a * b ≥ 0:= by positivity
  have g5 : c ^ 2 * a ^ 2 * (c + a) + c * a ≥ 0:= by positivity
  have g4 : b ^ 2 * c ^ 2 * (b + c) + b * c ≥ 0:= by positivity
  have g6 : a ^ 2 * b ^ 2 * (a + b) + a * b ≥ 0:= by positivity

  -- Apply division inequality to each term
  replace h1:= div_le_div_of_nonneg_left g1 (by positivity) h1
  replace h2:= div_le_div_of_nonneg_left g2 (by positivity) h2
  replace h3:= div_le_div_of_nonneg_left g3 (by positivity) h3

  -- Key step: Show that the sum with the denominators from our inequality equals 1
  have h4 : b * c / (b ^ 2 * c ^ 2 * (b + c) + b * c) + c * a / (c ^ 2 * a ^ 2 * (c + a) + c * a) + a * b / (a ^ 2 * b ^ 2 * (a + b) + a * b) = 1:= by
    rw [show a * b = (a * b * c) * (a * b) by rw [habc] ; simp]
    rw [show b * c = (a * b * c) * (b * c) by rw [habc] ; simp]
    rw [show c * a = (a * b * c) * (c * a) by rw [habc] ; simp]
    field_simp
    ring_nf

  -- Construct the conjunction for our theorem
  constructor
  -- First part: Prove the inequality
  .
    linarith

  -- Second part: Characterize when equality holds
  .
    constructor
    -- Forward direction: If equality holds, then a = b = c = 1
    .
      intro h5
      replace h1 : b * c / (b ^ 5 + c ^ 5 + b * c) = b * c / (b ^ 2 * c ^ 2 * (b + c) + b * c):= by linarith
      replace h2 : c * a / (c ^ 5 + a ^ 5 + c * a) = c * a / (c ^ 2 * a ^ 2 * (c + a) + c * a):= by linarith
      clear g1 g2 g3 g4 g5 g6 h4 h5
      field_simp at h1 h2

      -- From equality in the AM-GM inequality, we get b = c and c = a
      replace h1 : (b + c) * (b ^ 2 + b * c + c ^ 2) * (b - c) ^ 2 = 0:= by linarith
      replace h2 : (c + a) * (c ^ 2 + c * a + a ^ 2) * (c - a) ^ 2 = 0:= by linarith
      have g1 : (b + c) * (b ^ 2 + b * c + c ^ 2) ≠ 0:= by positivity
      have g2 : (c + a) * (c ^ 2 + c * a + a ^ 2) ≠ 0:= by positivity
      simp [g1] at h1
      simp [g2] at h2
      replace h1 : b = c:= by linarith
      replace h2 : c = a:= by linarith
      subst b c

      -- With a = b = c and abc = 1, we must have a = 1
      replace habc : (a - 1) * ((2 * a + 1) ^ 2 + 3) = 0:= by linarith
      have g3 : (2 * a + 1) ^ 2 + 3 ≠ 0:= by positivity
      simp [g3] at habc
      simp
      linarith

    -- Backward direction: If a = b = c = 1, then equality holds
    .
      rintro ⟨rfl, rfl, rfl⟩
      norm_num
