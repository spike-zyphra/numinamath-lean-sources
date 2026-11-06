import Mathlib

/- Let $z_1$ and $z_2$ be two complex numbers such that $|z_1| = 5$ and
\[\frac{z_1}{z_2} + \frac{z_2}{z_1} = 1.\]Find $|z_20495 - z_2|^2.$ -/
theorem algebra_20495 {z1 z2 : ℂ} (hz1 : ‖z1‖ = 5) (hz2 : z2 ≠ 0)
    (h : z1 / z2 + z2 / z1 = 1) : ‖z1 - z2‖ ^ 2 = 25 := by
  -- Let u = z2 / z1
  let u := z2 / z1
  -- The equation becomes u + u⁻¹ = 1
  replace h : u + u⁻¹ = 1 := by
    simp [u]
    linear_combination h
  -- u cannot be 0, as 0 + 0⁻¹ ≠ 1
  have un0 : u ≠ 0 := by
    intro hu
    simp [hu] at h
  field_simp at h
  -- Replace h as the standard form of a quadratic equation
  replace h : 1 * u * u + (-1) * u + 1 = 0 := by linear_combination h
  -- Write the discriminant of the quadratic equation as the square of a complex number
  have k : (discrim 1 (-1) 1 : ℂ) = {re := 0, im := √3} * {re := 0, im := √3} := by
    simp [discrim]
    change (1 - 4 : ℂ) = {re := 0 * 0 - √3 * √3, im := 0 * √3 + √3 * 0}
    norm_num
    apply Complex.ext <;> simp
  -- Solve the quadratic equation using the quadratic formula
  rw [mul_assoc, quadratic_eq_zero_iff (show (1 : ℂ) ≠ 0 by norm_num) k] at h
  -- The two solutions are (1 ± √3 i) / 2
  simp at h
  have h1 : (1 + { re := 0, im := √3 }) / (2 : ℂ) = { re := 1 / 2, im := √3 / 2 } := by
    apply Complex.ext <;> simp
  have h2 : (1 - { re := 0, im := √3 }) / (2 : ℂ) = { re := 1 / 2, im := -√3 / 2 } := by
    apply Complex.ext <;> simp
  rw [h1, h2] at h
  clear k h1 h2

  -- ‖1 - u‖ = 1, no matter which solution u is
  have hu : ‖1 - u‖ = 1 := by
    -- Calculate ‖1 - u‖ ^ 2
    simp [Complex.abs, Complex.normSq]
    clear_value u
    clear z1 z2 hz1 hz2 un0
    -- Case analysis on the two solutions
    rcases h with (rfl | rfl)
    all_goals
      -- Simplify the expression
      simp
      ring_nf
      norm_num

  -- Finally, calculate ‖z1 - z2‖ ^ 2
  calc ‖z1 - z2‖ ^ 2
       -- z1 - z2 = z1 * (1 - u)
       _ = ‖z1 * (1 - u)‖ ^ 2 := by
         congr
         simp only [u]
         field_simp [show z1 ≠ 0 by rintro rfl; simp at hz1]
       -- Use the multiplicative property of the norm
       _ = (‖z1‖ * ‖1 - u‖) ^ 2 := by rw [norm_mul]
       -- Plug in the values of ‖z1‖ and ‖1 - u‖
       _ = (5 * 1) ^ 2 := by rw [hz1, hu]
       -- Simplify
       _ = 25 := by norm_num
