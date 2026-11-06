import Mathlib

/- Let $\ a,x,y,z>0$. Prove that:
$\frac{a+y}{a+z}x+\frac{a+z}{a+x}y+\frac{a+x}{a+y}z\geq{x+y+z}\geq\frac{a+z}{a+x}x+\frac{a+x}{a+y}y+\frac{a+y}{a+z}z$ -/
theorem negated_inequalities_25390 (a x y z : ℝ)
    (ha : 0 < a)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (a + y) / (a + z) * x + (a + z) / (a + x) * y + (a + x) / (a + y) * z ≥ x + y + z ∧ x + y + z ≥ (a + z) / (a + x) * x + (a + x) / (a + y) * y + (a + y) / (a + z) * z := by 
  have hx1 : 0 < a + x := by linarith
  have hy1 : 0 < a + y := by linarith
  have hz1 : 0 < a + z := by linarith
  constructor 
  · -- Prove that $\frac{a+y}{a+z}x+\frac{a+z}{a+x}y+\frac{a+x}{a+y}z \geq x+y+z$
    have hx1' : 0 < (a + x) * (a + y) * (a + z) := by positivity
    have h1 : (a + y) / (a + z) * x + (a + z) / (a + x) * y + (a + x) / (a + y) * z - (x + y + z) ≥ 0 := by 
      have h2 : (a + y) / (a + z) * x + (a + z) / (a + x) * y + (a + x) / (a + y) * z - (x + y + z) =
          (x * (a + y) * (a + x) * (a + y) + y * (a + z) * (a + y) * (a + z) + z * (a + x) * (a + x) * (a + z) - (x + y + z) * (a + x) * (a + y) * (a + z)) / ((a + x) * (a + y) * (a + z)) := by
        field_simp
        ring
      rw [h2] at *
      apply div_nonneg
      · -- Show numerator is non-negative
        nlinarith [mul_pos ha hx, mul_pos ha hy, mul_pos ha hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
            sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
            sq_nonneg (a * x - a * y), sq_nonneg (a * y - a * z), sq_nonneg (a * z - a * x),
            mul_nonneg (show 0 ≤ a from by linarith) (show 0 ≤ a from by linarith), 
            sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
      · -- Show denominator is positive
        positivity 
    linarith [h1]
  · -- Prove that $x+y+z \geq \frac{a+z}{a+x}x+\frac{a+x}{a+y}y+\frac{a+y}{a+z}z$
    -- Similarly manipulate to clear denominators
    have hx1' : 0 < (a + x) * (a + y) * (a + z) := by positivity
    have h4 : x + y + z - ((a + z) / (a + x) * x + (a + x) / (a + y) * y + (a + y) / (a + z) * z) ≥ 0 := by 
      have h5 : x + y + z - ((a + z) / (a + x) * x + (a + x) / (a + y) * y + (a + y) / (a + z) * z) =
          ((x + y + z) * (a + x) * (a + y) * (a + z) - (x * (a + z) * (a + y) * (a + z) + y * (a + x) * (a + z) * (a + x) + z * (a + y) * (a + x) * (a + y))) / ((a + x) * (a + y) * (a + z)) := by
        field_simp
        ring 
      rw [h5] at *
      apply div_nonneg 
      · -- Show numerator is non-negative
        nlinarith [mul_pos ha hx, mul_pos ha hy, mul_pos ha hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
            sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
            sq_nonneg (a * x - a * y), sq_nonneg (a * y - a * z), sq_nonneg (a * z - a * x),
            mul_nonneg (show 0 ≤ a from by linarith) (show 0 ≤ a from by linarith), 
            sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
      · -- Show denominator is positive
        positivity 
    linarith [h4]