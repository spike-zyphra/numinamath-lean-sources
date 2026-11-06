import Mathlib

open Real

/- 152. Show that


$$

\cos \alpha + \cos \beta + \cos \gamma = 4 \sin \frac{\alpha}{2} \sin \frac{\beta}{2} \sin \frac{\gamma}{2} + 1

$$


and


$$

\cos \alpha + \cos \beta - \cos \gamma = 4 \cos \frac{\alpha}{2} \cos \frac{\beta}{2} \sin \frac{\gamma}{2} - 1

$$


if


$$

\alpha + \beta + \gamma = 180^{\circ}.

$$
 -/
theorem algebra_288849 (α β γ : ℝ) (h : α + β + γ = π) :
    cos α + cos β + cos γ = 4 * sin (α / 2) * sin (β / 2) * sin (γ / 2) + 1 ∧
    cos α + cos β - cos γ = 4 * cos (α / 2) * cos (β / 2) * sin (γ / 2) - 1 := by
  constructor
  -- for both sides, we do a simple calculation with basic trig identities
  · calc cos α + cos β + cos γ
    _ = cos α + cos β + cos (2 * ((π - α - β) / 2)) := by ring_nf; simp; apply congr_arg; linarith
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + cos (2 * ((π - α - β) / 2)) := by rw [cos_add_cos]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + (2 * cos ((π - α - β) / 2) ^ 2 - 1) := by rw [cos_two_mul]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + (2 * cos (π/2 - (α + β) / 2) ^ 2 - 1) := by ring_nf
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + (2 * sin ((α + β) / 2) ^ 2 - 1) := by rw [cos_pi_div_two_sub];
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + (2 * (sin ((α + β) / 2) ^ 2 + cos ((α + β) / 2) ^ 2 - cos ((α + β) / 2) ^ 2) - 1) := by ring_nf
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + (2 * (1 - cos ((α + β) / 2) ^ 2) - 1) := by rw [sin_sq_add_cos_sq]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + 1 - 2 * (cos ((α + β) / 2))^2 := by ring_nf
    _ = 2 * cos ((α + β) / 2) * (cos ((α - β) / 2) - cos ((α + β) / 2)) + 1 := by ring_nf
    _ = 2 * cos ((α + β) / 2) * (-2 * sin (α/2) * sin (-(β/2))) + 1 := by rw [cos_sub_cos]; ring_nf;
    _ = 2 * cos ((α + β) / 2) * (2 * sin (α/2) * sin (β/2)) + 1 := by rw [sin_neg]; ring_nf;
    _ = 4 * sin (α / 2) * sin (β / 2) * cos ((α + β) / 2) + 1 := by ring_nf;
    _ = 4 * sin (α / 2) * sin (β / 2) * cos ((π - γ) / 2) + 1 := by simp; left; apply congr_arg; linarith
    _ = 4 * sin (α / 2) * sin (β / 2) * cos (π/2 - γ / 2) + 1 := by ring_nf
    _ = 4 * sin (α / 2) * sin (β / 2) * sin (γ / 2) + 1 := by rw [cos_pi_div_two_sub];
  · calc cos α + cos β - cos γ
    _ = cos α + cos β - cos (2 * ((π - α - β) / 2)) := by ring_nf; simp; apply congr_arg; linarith
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - cos (2 * ((π - α - β) / 2)) := by rw [cos_add_cos]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - (2 * cos ((π - α - β) / 2) ^ 2 - 1) := by rw [cos_two_mul]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - (2 * cos (π/2 - (α + β) / 2) ^ 2 - 1) := by ring_nf
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - (2 * sin ((α + β) / 2) ^ 2 - 1) := by rw [cos_pi_div_two_sub];
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - (2 * (sin ((α + β) / 2) ^ 2 + cos ((α + β) / 2) ^ 2 - cos ((α + β) / 2) ^ 2) - 1) := by ring_nf
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) - (2 * (1 - cos ((α + β) / 2) ^ 2) - 1) := by rw [sin_sq_add_cos_sq]
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + 2 * (cos ((α + β) / 2))^2 - 1 := by ring_nf
    _ = 2 * cos ((α + β) / 2) * (cos ((α - β) / 2) + cos ((α + β) / 2)) - 1 := by ring_nf
    _ = 2 * cos ((α + β) / 2) * (2 * cos (α/2) * cos (-(β/2))) - 1 := by rw [cos_add_cos]; ring_nf;
    _ = 4 * cos ((α + β) / 2) * cos (α/2) * cos (β/2) - 1 := by rw [cos_neg]; ring_nf;
    _ = 4 * cos (α / 2) * cos (β / 2) * cos ((α + β) / 2) - 1 := by ring_nf;
    _ = 4 * cos (α / 2) * cos (β / 2) * cos ((π - γ) / 2) - 1 := by simp; left; apply congr_arg; linarith
    _ = 4 * cos (α / 2) * cos (β / 2) * cos (π/2 - γ / 2) - 1 := by ring_nf
    _ = 4 * cos (α / 2) * cos (β / 2) * sin (γ / 2) - 1 := by rw [cos_pi_div_two_sub]