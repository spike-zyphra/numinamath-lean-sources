import Mathlib

/- Simplify
\[\left( \frac{3 + i \sqrt{3}}{2} \right)^8 + \left( \frac{3 - i \sqrt{3}}{2} \right)^8.\] -/
theorem algebra_20260 :
  ((3 + Complex.I * Real.sqrt 3) / 2)^8 +
  ((3 - Complex.I * Real.sqrt 3) / 2)^8 = -81 := by
  -- let z = (3+√3i)/2 and w = (3-√3i)/2
  let z := (3 + Complex.I * Real.sqrt 3) / 2
  have z_def: z = (3 + Complex.I * Real.sqrt 3) / 2 := rfl
  let w := (3 - Complex.I * Real.sqrt 3) / 2
  have w_def: w = (3 - Complex.I * Real.sqrt 3) / 2 := rfl
  -- notice that it's easy to simplify zw
  have h1: z*w = 3 := by
    rw [z_def, w_def]
    ring_nf
    have: (√3:ℂ)^2 = 3 := by
      have: (√3:ℂ)^2 = ↑(√3 * √3) := by
        push_cast
        rw [pow_two]
      rw [this]; simp
    simp [Complex.I_mul_I, this]; ring
  -- also, easy to simplify z+w
  have h2: z+w = 3 := by
    rw [z_def, w_def]; ring
  -- (z+w)^2 = z^2+2zw+w^2, so we can simplify z^2+w^2
  have h3: z^2+w^2 = 3 := by
    have: z^2+w^2 = (z+w)^2 - 2*(z*w) := by ring
    rw [this, h2, h1]; ring
  -- square (z^2+w^2), we can simplify z^4+w^4
  have h4: z^4+w^4 = -9 := by
    have: z^4+w^4 = (z^2+w^2)^2 - 2*(z*w)^2 := by ring
    rw [this, h3, h1]; ring
  -- go on, square (z^4+w^4), we can simplify z^8+w^8
  have h5: z^8+w^8 = -81 := by
    have: z^8+w^8 = (z^4+w^4)^2 - 2*(z*w)^4 := by ring
    rw [this, h4, h1]; ring
  -- finally, we get the result
  rw [← z_def, ← w_def, h5]