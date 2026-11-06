import Mathlib
/- Soit $a, b, c$ des réels strictement positifs tels que : $a b+b c+c a=a b c$. Montrer que :

$$
\frac{1}{a^{2}+b^{2}}+\frac{1}{b^{2}+c^{2}}+\frac{1}{c^{2}+a^{2}} \leqslant \frac{1}{6},
$$

et trouver les cas d'égalité. -/
theorem algebra_607254 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b + b * c + c * a = a * b * c) :
1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / 6 ∧ (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) = 1 / 6 ↔ (a = 3 ∧ b = 3 ∧ c = 3)):= by

  -- Transform the initial equation to show that 1/a + 1/b + 1/c = 1
  replace h : 1 / a + 1 / b + 1 / c = 1:= by
    field_simp
    linarith

  -- Define substitution variables for simplification
  set x:= 1 / a with hx
  set y:= 1 / b with hy
  set z:= 1 / c with hz

  -- Express the first fraction in terms of x and y
  have h1 : 1 / (a ^ 2 + b ^ 2) = x ^ 2 * y ^ 2 / (x ^ 2 + y ^ 2):= by
    rw [hx, hy]
    field_simp
    linarith

  -- Express the second fraction in terms of y and z
  have h2 : 1 / (b ^ 2 + c ^ 2) = y ^ 2 * z ^ 2 / (y ^ 2 + z ^ 2):= by
    rw [hy, hz]
    field_simp
    linarith

  -- Express the third fraction in terms of z and x
  have h3 : 1 / (c ^ 2 + a ^ 2) = z ^ 2 * x ^ 2 / (z ^ 2 + x ^ 2):= by
    rw [hz, hx]
    field_simp
    linarith

  -- Clean up unnecessary variables and hypotheses
  rw [h1, h2, h3]
  clear_value x y z
  clear h1 h2 h3

  -- Key inequality lemma for any two positive real numbers
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x ^ 2 * y ^ 2 / (x ^ 2 + y ^ 2) ≤ 1 / 2 * x * y:= by
    intro x y hx hy
    have g1 : x ^ 2 + y ^ 2 > 0:= by positivity
    suffices (x ^ 2 * y ^ 2 / (x ^ 2 + y ^ 2)) * (x ^ 2 + y ^ 2) ≤ 1 / 2 * x * y * (x ^ 2 + y ^ 2) by exact le_of_mul_le_mul_right this g1
    rw [show (x ^ 2 * y ^ 2 / (x ^ 2 + y ^ 2)) * (x ^ 2 + y ^ 2) = x ^ 2 * y ^ 2 by field_simp]
    have g2 : x * y * (x - y) ^ 2 ≥ 0:= by positivity
    linarith

  -- Establish positivity of substitution variables
  have hxpos : x > 0:= by rw [hx] ; positivity
  have hypos : y > 0:= by rw [hy] ; positivity
  have hzpos : z > 0:= by rw [hz] ; positivity

  -- Apply the key inequality to each pair of variables
  have h2:= h1 x y hxpos hypos
  have h3:= h1 y z hypos hzpos
  have h4:= h1 z x hzpos hxpos

  -- Non-negativity of sum of squared differences
  have h5 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0:= by positivity

  -- Square of sum equals 1 from earlier substitution
  have h6 : (x + y + z) ^ 2 = 1:= by
    rw [h]
    ring_nf

  -- Split into two parts: inequality and equality cases
  constructor
  .
    rw [←h6]
    linarith
  .
    constructor
    .
      -- Forward direction: if equality holds, then a = b = c = 3
      intro hgoal
      rw [←h6] at hgoal
      replace h5 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0:= by linarith
      have g1 : (x - y) ^ 2 ≥ 0:= by positivity
      have g2 : (y - z) ^ 2 ≥ 0:= by positivity
      have g3 : (z - x) ^ 2 ≥ 0:= by positivity
      replace g1 : (x - y) ^ 2 = 0:= by linarith
      replace g2 : (y - z) ^ 2 = 0:= by linarith
      replace g1 : x - y = 0:= by exact pow_eq_zero g1
      replace g2 : y - z = 0:= by exact pow_eq_zero g2
      have gx : x = 1 / 3:= by linarith
      have gy : y = 1 / 3:= by linarith
      have gz : z = 1 / 3:= by linarith
      rw [gx] at hx
      rw [gy] at hy
      rw [gz] at hz
      field_simp at hx hy hz
      subst a b c
      simp
    .
      -- Reverse direction: if a = b = c = 3, then equality holds
      intro hgoal
      rcases hgoal with ⟨ga, gb, gc⟩
      subst a b c
      subst x y z
      ring_nf
