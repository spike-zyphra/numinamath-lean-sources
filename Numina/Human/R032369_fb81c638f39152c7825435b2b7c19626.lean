import Mathlib

/- Given $\sin \alpha= \frac {4}{5}$, and $\alpha$ is an acute angle, then $\cos \frac {\alpha}{2}=$　　()
A: $ \frac { \sqrt {5}}{5}$
B: $ \frac {2 \sqrt {5}}{5}$
C: $ \frac {3 \sqrt {5}}{5}$
D: $ \frac { \sqrt {3}}{2}$ -/
theorem algebra_347662 (α : ℝ) (h₀ : Real.sin α = 4 / 5) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (α / 2) = 2 * √5 / 5 := by
  have h₂ : Real.cos α = 3 / 5 := by
    have h₂ : 0 < Real.cos α := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      . linarith only [h₁.1, Real.pi_pos]
      . exact h₁.2
    have h₃ := Real.cos_sq_add_sin_sq α
    rw [h₀] at h₃
    nlinarith
  have h₃ : 0 < Real.cos (α / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    . linarith only [h₁.1, Real.pi_pos]
    . linarith only [h₁.2, Real.pi_pos]
  have h₄ := Real.cos_sq (α / 2)
  rw [show 2 * (α / 2) = α by ring] at h₄
  norm_num [h₂] at h₄
  have h₅ : 4 / 5 = (2 * √5 / 5) ^ 2 := by
    ring_nf
    norm_num
  have h₆ : 2 * √5 / 5 > 0 := by positivity
  rw [h₅, sq_eq_sq₀ (le_of_lt h₃) (le_of_lt h₆)] at h₄
  exact h₄
