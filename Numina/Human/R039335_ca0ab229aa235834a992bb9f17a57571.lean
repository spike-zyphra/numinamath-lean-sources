import Mathlib
/- 2. let $a, b$ and $c$ be the sides of a triangle, that is: $a+b>c, b+c>a$ and $c+a>b$. Show that holds:

$$
\frac{a b+1}{a^{2}+c a+1}+\frac{b c+1}{b^{2}+a b+1}+\frac{c a+1}{c^{2}+b c+1}>\frac{3}{2}
$$ -/
theorem inequalities_266077 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) :
3 / 2 < (a * b + 1) / (a ^ 2 + c * a + 1) + (b * c + 1) / (b ^ 2 + a * b + 1) +
(c * a + 1) / (c ^ 2 + b * c + 1):= by
  -- Helper lemma: For positive reals x,y,z where y+z>x, we have (z*x+1)/(z²+y*z+1) > x/(y+z)
  have h4 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → y + z - x > 0 → (z * x + 1) / (z ^ 2 + y * z + 1) > x / (y + z):= by
    intro x y z _ hy hz h1
    -- Rewrite the left side using algebraic manipulation
    rw [show (z * x + 1) / (z ^ 2 + y * z + 1) = 1 - z * (y + z - x) / (z ^ 2 + y * z + 1) by field_simp ; ring_nf]
    -- Prove that z² + y*z + 1 > z² + y*z
    have h2 : z ^ 2 + y * z + 1 > z ^ 2 + y * z:= by linarith
    -- Show that z² + y*z > 0
    have g1 : z ^ 2 + y * z > 0:= by positivity
    -- Show that z*(y+z-x) > 0
    have g2 : z * (y + z - x) > 0:= by positivity
    -- Apply division inequality
    have g3 : z * (y + z - x) / (z ^ 2 + y * z + 1) < z * (y + z - x) / (z ^ 2 + y * z):= by exact div_lt_div_of_pos_left g2 g1 h2
    -- Prove that 1 - z*(y+z-x)/(z²+y*z) = x/(y+z)
    suffices 1 - z * (y + z - x) / (z ^ 2 + y * z) = x / (y + z) by linarith
    field_simp
    linarith

  -- Apply the helper lemma to each pair of sides
  have g1:= h4 a b c ha hb hc (by linarith)
  have g2:= h4 b c a hb hc ha (by linarith)
  have g3:= h4 c a b hc ha hb (by linarith)

  -- Reduce to proving a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2
  suffices a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 by linarith
  clear g1 g2 g3 h1
  field_simp

  -- Show that the product of denominators is positive
  have g1 : (b + c) * (c + a) * (a + b) > 0:= by positivity

  -- Convert the inequality to a form suitable for algebraic manipulation
  suffices 3 / 2 * ((b + c) * (c + a) * (a + b)) ≤ (a * (c + a) + b * (b + c)) * (a + b) + c * ((b + c) * (c + a)) by exact (le_div_iff₀ g1).mpr this

  -- Use the fact that sum of squared differences weighted by sums is non-negative
  have g2 : (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 + (a + b) * (a - b) ^ 2 ≥ 0:= by positivity
  linarith
