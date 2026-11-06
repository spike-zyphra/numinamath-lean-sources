import Mathlib

/- Prove that:
$ \frac {x^{2}y}{z} \plus{} \frac {y^{2}z}{x} \plus{} \frac {z^{2}x}{y}\geq x^{2} \plus{} y^{2} \plus{} z^{2}$
where $ x;y;z$ are real numbers saisfying $ x \geq y \geq z \geq 0$ -/
theorem negated_inequalities_75505 {x y z : ℝ} 
    (hz : 0 < z) (hzx : z ≤ y) (hxy : y ≤ x) :
    x^2 * y / z + y^2 * z / x + z^2 * x / y ≥ x^2 + y^2 + z^2 := by
  -- Show that x, y are positive
  have hx : 0 < x := by
    nlinarith [show 0 < z by linarith, show z ≤ y by linarith, show y ≤ x by linarith]
  have hy : 0 < y := by
    nlinarith [show 0 < z by linarith, show z ≤ y by linarith]
  -- Show that x * y * z is positive
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  -- Show that the difference of the two sides is non-negative
  have h2 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) ≥ 0 := by
    -- Express the difference as a single fraction
    have h3 : x^2 * y / z + y^2 * z / x + z^2 * x / y - (x^2 + y^2 + z^2) =
        (x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z) := by 
      field_simp
      ring
    rw [h3] at *
    -- Show the numerator is non-negative
    have h4 : (x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^2 + y^2 + z^2) * (x * y * z)) ≥ 0 := by 
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (y - z)), 
          sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (y * (x - z)), 
          sq_nonneg (z * (x - y)), sq_nonneg (z * (y - z)), sq_nonneg (z * (x - z)), 
          mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ y - z by linarith), 
          mul_nonneg (show 0 ≤ y - z by linarith) (show 0 ≤ x - y by linarith), 
          mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x - y by linarith), 
          mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x - y by linarith), 
          mul_nonneg (show 0 ≤ (y - z) by linarith) (show 0 ≤ (x - y) by linarith), 
          mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ (x - z) by linarith)
        ]
    -- Show the entire fraction is non-negative
    have hxyz_pos : 0 < x * y * z := h1
    have hfrac : ((x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z)) ≥ 0 := by 
      apply div_nonneg 
      linarith
      positivity
    linarith 
  -- Conclude the proof
  linarith
  all_goals try { nlinarith }
  all_goals try { nlinarith }