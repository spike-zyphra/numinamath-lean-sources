import Mathlib

open Real Set

/- Given that $\sin \alpha + \cos \alpha = \frac{1}{5}$, where $0 \leqslant \alpha \leqslant \pi$, the value of $\sqrt{2}\sin \left( 2\alpha -\frac{\pi }{4} \right)$ is (    )
A: $-\frac{31}{25}$
B: $-\frac{17}{25}$
C: $\pm \frac{31}{25}$
D: $\pm \frac{17}{25}$ -/
theorem algebra_520979 (α : ℝ) (h₁ : α ∈ Icc 0 π) (h₂ : sin α + cos α = 1 / 5) :
    √2 * sin (2 * α - π / 4) = -17 / 25 := by
  obtain ⟨h₃, h₄⟩ : sin α = 4 / 5 ∧ cos α = -(3 / 5) := by
    have h₃ : cos α = 1 / 5 - sin α := by linarith only [h₂]
    have h₄ := cos_sq_add_sin_sq α
    rw [h₃] at h₄
    have h₅ : 0 ≤ sin α := sin_nonneg_of_mem_Icc h₁
    have h₆ : sin α = 4 / 5 := by nlinarith only [h₄, h₅]
    norm_num [h₆] at h₃
    exact ⟨h₆, h₃⟩
  simp [sin_sub]
  ring_nf
  simp
  ring_nf
  rw [show α * 2 = 2 * α by ring, sin_two_mul, cos_two_mul]
  norm_num [h₃, h₄]
