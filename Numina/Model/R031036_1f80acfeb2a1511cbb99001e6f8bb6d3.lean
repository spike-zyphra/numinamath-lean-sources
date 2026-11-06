import Mathlib


open Real Set


theorem algebra_181840 (α β γ : ℝ) :
  sin α + sin β + sin γ - sin (α + β + γ) =
  4 * sin ((α + β) / 2) * sin ((β + γ) / 2) * sin ((γ + α) / 2) ∧
  cos α + cos β + cos γ + cos (α + β + γ) =
  4 * cos ((α + β) / 2) * cos ((β + γ) / 2) * cos ((γ + α) / 2) := by
  constructor
  · -- Prove the first part: $\sin \alpha + \sin \beta + \sin \gamma - \sin (\alpha + \beta + \gamma) = 4 \sin \frac{\alpha + \beta}{2} \sin \frac{\beta + \gamma}{2} \sin \frac{\gamma + \alpha}{2}$
    have h1 : sin (α + β + γ) = sin α * cos β * cos γ + cos α * sin β * cos γ + cos α * cos β * sin γ - sin α * sin β * sin γ := by
      have h3 : sin (α + β + γ) = sin ((α + β) + γ) := by ring
      rw [h3]
      rw [sin_add]
      rw [sin_add, cos_add]
      ring
    rw [h1]
    have h2 : sin ((α + β) / 2) = sin (α / 2 + β / 2) := by
      ring_nf
    have h9 : sin (α / 2 + β / 2) = sin (α / 2) * cos (β / 2) + cos (α / 2) * sin (β / 2) := by
      rw [sin_add]
    have h10 : sin ((β + γ) / 2) = sin (β / 2 + γ / 2) := by
      ring_nf
    have h11 : sin (β / 2 + γ / 2) = sin (β / 2) * cos (γ / 2) + cos (β / 2) * sin (γ / 2) := by
      rw [sin_add]
    have h12 : sin ((γ + α) / 2) = sin (γ / 2 + α / 2) := by
      ring_nf
    have h13 : sin (γ / 2 + α / 2) = sin (γ / 2) * cos (α / 2) + cos (γ / 2) * sin (α / 2) := by
      rw [sin_add]
    have h21 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
      rw [←sin_two_mul]
      ring_nf
    have h22 : sin β = 2 * sin (β / 2) * cos (β / 2) := by
      rw [←sin_two_mul]
      ring_nf
    have h23 : sin γ = 2 * sin (γ / 2) * cos (γ / 2) := by
      rw [←sin_two_mul]
      ring_nf
    have h5 : cos α = 2 * cos (α / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    have h6 : cos β = 2 * cos (β / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    have h7 : cos γ = 2 * cos (γ / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    rw [h21, h22, h23, h5, h6, h7, h2, h9, h10, h11, h12, h13]
    ring_nf
    <;> simp [sin_sq, cos_sq, mul_add, add_mul, mul_assoc]
    <;> ring
  · -- Prove the second part: $\cos \alpha + \cos \beta + \cos \gamma + \cos (\alpha + \beta + \gamma) = 4 \cos \frac{\alpha + \beta}{2} \cos \frac{\beta + \gamma}{2} \cos \frac{\gamma + \alpha}{2}$
    have h14 : cos (α + β + γ) = cos α * cos β * cos γ - sin α * sin β * cos γ - sin α * cos β * sin γ - cos α * sin β * sin γ := by
      have h15 : cos (α + β + γ) = cos ((α + β) + γ) := by ring
      rw [h15]
      rw [cos_add]
      rw [cos_add, sin_add]
      ring
    rw [h14]
    have h15 : cos ((α + β) / 2) = cos (α / 2 + β / 2) := by
      ring_nf
    have h16 : cos (α / 2 + β / 2) = cos (α / 2) * cos (β / 2) - sin (α / 2) * sin (β / 2) := by
      rw [cos_add]
    have h17 : cos ((β + γ) / 2) = cos (β / 2 + γ / 2) := by
      ring_nf
    have h18 : cos (β / 2 + γ / 2) = cos (β / 2) * cos (γ / 2) - sin (β / 2) * sin (γ / 2) := by
      rw [cos_add]
    have h19 : cos ((γ + α) / 2) = cos (γ / 2 + α / 2) := by
      ring_nf
    have h20 : cos (γ / 2 + α / 2) = cos (γ / 2) * cos (α / 2) - sin (γ / 2) * sin (α / 2) := by
      rw [cos_add]
    have h21 : cos α = 2 * cos (α / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    have h22 : cos β = 2 * cos (β / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    have h23 : cos γ = 2 * cos (γ / 2) ^ 2 - 1 := by
      rw [←cos_two_mul]
      ring_nf
    have h24 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
      rw [←sin_two_mul]
      ring_nf
    have h25 : sin β = 2 * sin (β / 2) * cos (β / 2) := by
      rw [←sin_two_mul]
      ring_nf
    have h26 : sin γ = 2 * sin (γ / 2) * cos (γ / 2) := by
      rw [←sin_two_mul]
      ring_nf
    rw [h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
    ring_nf
    <;> simp [sin_sq, cos_sq, mul_add, add_mul, mul_assoc]
    <;> ring