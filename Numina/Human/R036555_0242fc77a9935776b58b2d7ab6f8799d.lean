import Mathlib
/- Нека су $x, y, z$ позитивни реални бројеви такви да је $x y+y z+z x=x+y+z$. Доказати неједнакост

$$
\frac{1}{x^{2}+y+1}+\frac{1}{y^{2}+z+1}+\frac{1}{z^{2}+x+1} \leqslant 1
$$

Када се у претходној неједнакости достиже знак једнакости?

(Марко Радовановић) -/
theorem inequalities_608064 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x = x + y + z) : 1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) ≤ 1 ∧ (1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) = 1 ↔ x = 1 ∧ y = 1 ∧ z = 1):= by
  -- Cauchy-Schwarz inequality: For positive reals, the product of sums of squares
  -- is greater than or equal to the square of the sum of products
  have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
  (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
    -- This is derived from the fact that sum of squares is non-negative
    have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
    linarith

  -- Apply Cauchy-Schwarz with specific values for the first triple of inequalities
  have g1:= h1 x √y 1 1 √y z (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  -- Apply Cauchy-Schwarz with specific values for the second triple of inequalities
  have g2:= h1 y √z 1 1 √z x (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  -- Apply Cauchy-Schwarz with specific values for the third triple of inequalities
  have g3:= h1 z √x 1 1 √x y (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

  -- Simplify the field expressions
  field_simp at g1 g2 g3

  -- Convert the inequalities to the form we need using the one_le_div₀ lemma
  replace g1:= (one_le_div₀ (by positivity)).mpr g1
  replace g2:= (one_le_div₀ (by positivity)).mpr g2
  replace g3:= (one_le_div₀ (by positivity)).mpr g3

  -- Rewrite expressions to prepare for combining the inequalities
  rw [show (x ^ 2 + y + 1) * (1 + y + z ^ 2) / (x + y + z) ^ 2 = (x ^ 2 + y + 1) * ((1 + y + z ^ 2) / (x + y + z) ^ 2) by ring] at g1
  rw [show (y ^ 2 + z + 1) * (1 + z + x ^ 2) / (y + z + x) ^ 2 = (y ^ 2 + z + 1) * ((1 + z + x ^ 2) / (y + z + x) ^ 2) by ring] at g2
  rw [show (z ^ 2 + x + 1) * (1 + x + y ^ 2) / (z + x + y) ^ 2 = (z ^ 2 + x + 1) * ((1 + x + y ^ 2) / (z + x + y) ^ 2) by ring] at g3

  -- Transform the inequalities using division properties
  replace g1:= (div_le_iff₀' (by positivity)).mpr g1
  replace g2:= (div_le_iff₀' (by positivity)).mpr g2
  replace g3:= (div_le_iff₀' (by positivity)).mpr g3
  -- Establish a sufficient condition for the original inequality
  have h2 : (1 + y + z ^ 2) / (x + y + z) ^ 2 + (1 + z + x ^ 2) / (y + z + x) ^ 2 + (1 + x + y ^ 2) / (z + x + y) ^ 2 ≤ 1:= by
    -- Clear unnecessary hypotheses
    clear h1 g1 g2 g3

    -- Rewrite expressions to standardize the denominators
    rw [show y + z + x = x + y + z by ring]
    rw [show z + x + y = x + y + z by ring]

    -- Combine fractions with common denominator
    rw [show (1 + y + z ^ 2) / (x + y + z) ^ 2 + (1 + z + x ^ 2) / (x + y + z) ^ 2 + (1 + x + y ^ 2) / (x + y + z) ^ 2 = ((1 + y + z ^ 2) + (1 + z + x ^ 2) + (1 + x + y ^ 2)) / (x + y + z) ^ 2 by field_simp]

    -- Reduce to comparing numerator and denominator
    suffices (1 + y + z ^ 2 + (1 + z + x ^ 2) + (1 + x + y ^ 2)) ≤ (x + y + z) ^ 2 by exact (div_le_one₀ (by positivity)).mpr this

    -- Further reduce to showing x + y + z ≥ 3
    suffices x + y + z ≥ 3 by linarith

    -- Apply AM-GM inequality to show that 3(xy + yz + zx) ≤ (x+y+z)²
    have h1 : 3 * (x * y + y * z + z * x) ≤ (x + y + z) * (x + y + z):= by
      suffices (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 by linarith
      positivity

    -- Use the original condition to complete the proof
    rw [h] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  constructor
  -- Prove the first part of the conjunction: the inequality holds
  .
    linarith
  -- Prove the second part: characterizing when equality holds
  .
    constructor
    -- First direction: if equality holds, then x = y = z = 1
    .
      intro h3
      -- From the equality case, we get that the sum of our three fractions equals 1
      replace h2 : (1 + y + z ^ 2) / (x + y + z) ^ 2 + (1 + z + x ^ 2) / (y + z + x) ^ 2 + (1 + x + y ^ 2) / (z + x + y) ^ 2 = 1:= by linarith
      clear g1 g2 g3 h1
      -- Standardize the denominators
      rw [show y + z + x = x + y + z by ring] at h2
      rw [show z + x + y = x + y + z by ring] at h2
      field_simp at h2
      -- From the equality case, we deduce that x + y + z = 3
      replace h2 : x + y + z = 3:= by linarith
      rw [h2] at h
      -- Using the original condition and x + y + z = 3, we show that the sum of squares equals zero
      replace h : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0:= by
        suffices (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x) = 0 by linarith
        rw [h, h2]
        linarith
      -- Since sum of squares equals zero and each square is non-negative, each square must be zero
      have g1 : (x - y) ^ 2 = 0:= by linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      have g2 : (y - z) ^ 2 = 0:= by linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      -- Simplify to get x = y and y = z
      simp at g1 g2
      -- Conclude that x = y = z = 1 using the conditions x = y, y = z, and x + y + z = 3
      refine ⟨(by linarith), (by linarith), (by linarith)⟩
    -- Second direction: if x = y = z = 1, then equality holds
    .
      rintro ⟨rfl, rfl, rfl⟩
      -- Normalize the numerical expression to verify equality
      norm_num
