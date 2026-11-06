import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151827 {α : ℝ} (f g : ℝ → ℝ)
  (hf : f = λ x => exp x) (hg : g = λ x => α * x ^ 2)
  (hfg : ∃ x, deriv f x = deriv g x ∧ f x = g x) :
  α = exp 2 / 4 := by
  rcases hfg with ⟨x, h1, h2⟩
  have eq1 : deriv f x = exp x := by
    rw [hf]
    simp
  have eq2 : deriv g x = 2 * α * x := by
    rw [hg]
    simp [deriv_const_mul, deriv_pow]
    ring
  have eq3 : exp x = 2 * α * x := by 
    linarith [h1, eq1, eq2]
  have eq4 : exp x = α * x ^ 2 := by
    rw [hf] at h2
    rw [hg] at h2
    simp at h2
    linarith
  by_cases h : α = 0
  · -- Case $\alpha = 0$
    rw [h] at eq3 eq4
    have h3 : exp x > 0 := exp_pos x
    nlinarith
  · -- Case $\alpha \neq 0$
    have eq5 : exp x > 0 := exp_pos x
    have eq6 : α * x ^ 2 = 2 * α * x := by
      linarith [eq3, eq4]
    have eq7 : α * (x ^ 2 - 2 * x) = 0 := by
      linarith [eq6]
    have eq8 : x ^ 2 - 2 * x = 0 := by
      apply (mul_left_inj' h).mp
      linarith [eq7]
    have eq9 : x * (x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq9) with eq10 eq11
    · -- Case $x = 0$
      have hx0 : x = 0 := by
        linarith
      rw [hx0] at eq3
      norm_num at eq3
      all_goals linarith [exp_pos 0]
    · -- Case $x - 2 = 0$ (i.e., $x = 2$)
      have hx2 : x = 2 := by
        linarith
      rw [hx2] at eq3
      nlinarith [exp_pos 2]