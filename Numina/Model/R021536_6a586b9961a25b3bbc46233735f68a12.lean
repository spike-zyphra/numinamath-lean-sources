import Mathlib

open Real Set
open scoped Real

theorem algebra_317324 {x : ℝ} :
  sin x ^ 4 - cos x ^ 4 = 1 ↔ ∃ k : ℤ, x = k * π + π / 2 := by
  constructor
  · -- Assume sin x ^ 4 - cos x ^ 4 = 1, prove ∃ k : ℤ, x = k * π + π / 2
    intro h
    have eq1 : sin x ^ 4 - cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) * (sin x ^ 2 - cos x ^ 2) := by
      ring
    have h1 : sin x ^2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    rw [eq1, h1] at h
    -- Now h is sin x^2 - cos x^2 = 1
    have eq2 : sin x ^ 2 = 1 + cos x ^ 2 := by
      nlinarith
    have eq3 : cos x ^ 2 = 0 := by
      have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      nlinarith [eq2, h2]
    -- $\cos x = 0$
    have eq4 : cos x = 0 := by
      nlinarith [eq3]
    -- $\cos x = 0$ implies that $x = k\pi + \pi/2$ for some integer $k$
    rcases Real.cos_eq_zero_iff.1 eq4 with ⟨k, hk⟩
    refine ⟨k, by linarith [hk]⟩
  · -- Assume ∃ k : ℤ, x = k * π + π / 2, prove sin x ^ 4 - cos x ^ 4 = 1
    rintro ⟨k, hk⟩
    have hcos : cos x = 0 := by 
      rw [show x = (k : ℝ) * π + π / 2 by linarith [hk]]
      have hk1 : cos ((↑k : ℝ) * π + π / 2) = 0 := by
        have h1 : cos ((↑k : ℝ) * π + π / 2) = cos ((↑k : ℝ) * π) * cos (π / 2) - sin ((↑k : ℝ) * π) * sin (π / 2) := by
          rw [cos_add]
        rw [h1]
        have h3 : sin (π / 2) = 1 := by
          exact sin_pi_div_two
        have h4 : cos (π / 2) = 0 := by
          exact cos_pi_div_two
        simp [h3, h4]
        all_goals
          simp [sin_int_mul_pi, cos_int_mul_pi]
      linarith
    have eq1 : sin x ^ 4 - cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) * (sin x ^ 2 - cos x ^ 2) := by
      ring
    have h1 : sin x ^2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    rw [eq1, h1] 
    have eq4 : sin x ^ 2 = 1 := by
      have h7 : cos x = 0 := hcos
      have h6 : sin x ^ 2 + cos x ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq x
      rw [h7] at h6 
      nlinarith
    nlinarith [eq4, hcos]