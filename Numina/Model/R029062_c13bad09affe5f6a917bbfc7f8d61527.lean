import Mathlib

open Real Set
open scoped Real

theorem calculus_63704 : IsGreatest {x | ∃ θ : ℝ, x = sin θ ^ 4 + cos θ ^ 6} 1 := by
  constructor
  · -- $1 \in \{x \mid \exists \theta : \mathbb{R}, x = \sin \theta ^ 4 + \cos \theta ^ 6\}$
    use Real.pi / 2
    have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have h2 : cos (Real.pi / 2) = 0 := by
      rw [Real.cos_pi_div_two]
    rw [h1, h2]
    norm_num
  · -- $\forall x \in \{x \mid \exists \theta : \mathbb{R}, x = \sin \theta ^ 4 + \cos \theta ^ 6\}, x \le 1$
    intro x hx
    rcases hx with ⟨θ, h⟩
    rw [h]
    have h1 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    have h2 : sin θ ^ 4 + cos θ ^ 6 ≤ 1 := by
      nlinarith [sq_nonneg (sin θ ^ 2 - 0), sq_nonneg (cos θ ^ 2 - 1), 
        sq_nonneg (sin θ ^ 2 - cos θ ^ 2), 
        sq_nonneg (sin θ ^ 2 - 1), sq_nonneg (cos θ ^ 2 - 0), 
        sq_nonneg (sin θ), sq_nonneg (cos θ), 
        sq_nonneg (sin θ ^ 2 + cos θ ^ 2 - 1), 
        mul_nonneg (show 0 ≤ (sin θ ^ 2) by positivity) 
          (show 0 ≤ (cos θ ^ 2) by positivity)
      ]
    linarith [h2]