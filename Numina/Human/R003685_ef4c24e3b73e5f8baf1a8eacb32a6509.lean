import Mathlib

open Real

/- 7.1. Calculate: $4\left(\sin ^{3} \frac{49 \pi}{48} \cos \frac{49 \pi}{16}+\cos ^{3} \frac{49 \pi}{48} \sin \frac{49 \pi}{16}\right) \cos \frac{49 \pi}{12}$. -/
theorem algebra_207361 : 4 * (sin (49 * π / 48) ^ 3 * cos (49 * π / 16) + cos (49 * π / 48) ^ 3 * sin (49 * π / 16)) * cos (49 * π / 12) = 0.75 := by
  -- we first note that 49*pi/48 = pi/48 + pi. We also denote the angle with α
  have h0: 49 * π / 48 = π / 48 + π := by ring
  let q:∃ α:ℝ, α = 49*π/48 := by
    simp only [exists_eq]
  obtain ⟨α, αdef⟩ := q
  calc 4 * (sin (49 * π / 48) ^ 3 * cos (49 * π / 16) + cos (49 * π / 48) ^ 3 * sin (49 * π / 16)) * cos (49 * π / 12)
  _ = 4 * (sin (α) ^ 3 * cos (3*α) + cos (α) ^ 3 * sin (3*α)) * cos (4*α) := by rw [αdef]; ring_nf
  -- cos(3*α) = 4cos^3(α) - 3cos(α)
  _ = 4 * (sin (α) ^ 3 * (4*cos (α)^3-3*cos (α)) + cos (α) ^ 3 * (3*sin (α) - 4*sin (α)^3)) * cos (4*α) := by rw [Real.cos_three_mul, Real.sin_three_mul]
  _ = 4 * (-3*sin (α) ^ 3 * cos (α) + 3*cos (α) ^3 * sin (α)) * cos (4*α) := by ring_nf
  _ = 4 * (3*sin (α) * cos (α) * (cos (α) ^ 2 - sin (α) ^ 2)) * cos (4*α) := by ring_nf
  -- cos(α)^2 - sin(α)^2 = cos(2*α)
  -- sin(α) * cos(α) = 1/2 sin(2*α)
  _ = 4 * (3* sin (2*α) / 2 * cos (2*α)) * cos (4*α) := by rw [Real.sin_two_mul, Real.cos_two_mul']; ring_nf
  _ = 6 * sin (2*α) * cos (2*α) * cos (4*α) := by ring_nf
  _ = 3 * sin (2*(2*α)) * cos (4*α) := by rw [Real.sin_two_mul (x:=2*α)]; ring_nf
  _ = 3 * sin (4*α) * cos (4*α) := by ring_nf
  _ = 3 / 2 * sin (2*(4*α)) := by rw [Real.sin_two_mul]; ring_nf
  _ = 3 / 2 * sin (8*α) := by ring_nf
  -- revert back to the original angle and calculate
  _ = 3 / 2 * sin (8*(π/48 + π)) := by rw [αdef]; ring_nf
  _ = 3 / 2 * sin (8*π/48 + (4:ℕ) * (2*π)) := by ring_nf
  _ = 3 / 2 * sin (π/6) := by rw [Real.sin_add_nat_mul_two_pi]; ring_nf
  _ = 3 / 2 * (1/2) := by rw [Real.sin_pi_div_six]
  _ = 0.75 := by norm_num