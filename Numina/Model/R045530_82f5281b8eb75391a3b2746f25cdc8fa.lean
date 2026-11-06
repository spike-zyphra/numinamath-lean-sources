import Mathlib

open Real

theorem calculus_70485 (α : ℝ) (h : ∃ x, exp x = α * x ^ 2 ∧ deriv exp x = deriv (fun x => α * x ^ 2) x) :
    α = exp 2 / 4 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h1 : deriv exp x = exp x := by simp
  have h2 : deriv (fun (y : ℝ) => α * y ^ 2) x = 2 * α * x := by
    simp [deriv_const_mul, deriv_pow]
    <;> ring_nf <;> field_simp <;> ring
  rw [h1, h2] at hx2
  by_cases hα : α = 0
  · -- α = 0
    rw [hα] at hx1 hx2
    have h3 : exp x > 0 := by positivity
    nlinarith
  · -- α ≠ 0
    have eq1 : α * x ^ 2 = 2 * α * x := by
      nlinarith [hα]
    have hx2a : x ^ 2 = 2 * x := by
      apply (mul_left_inj' hα).mp
      linarith
    have h3 : x * (x - 2) = 0 := by 
      linarith [hx2a]
    cases' (mul_eq_zero.mp h3) with hx4 hx5
    · -- x = 0
      have hx0 : x = 0 := by linarith
      rw [hx0] at hx1
      norm_num at hx1
      all_goals linarith [exp_pos (x), exp_pos (0)]
    · -- x - 2 = 0
      have hx2b : x = 2 := by linarith
      rw [hx2b] at hx1 hx2
      have hα2 : α = exp (2:ℝ) / 4 := by
        nlinarith [exp_pos (2:ℝ)]
      linarith