import Mathlib

theorem calculus_308940 (f : ℝ → ℝ) (m : ℝ) (hf : f = fun x => x ^ 2 + m * x + 1)
    (P : ℝ × ℝ) (hP : P.1 = 0 ∧ P.2 = -3) :
    deriv f 2 * (P.1 - 2) + f 2 = P.2 := by

  rcases hP with ⟨hx1, hx2⟩
  have hf2 : f 2 = 2 ^ 2 + m * 2 + 1 := by
    rw [hf]
  have hf2_val : f 2 = 2 * m + 5 := by
    rw [hf2]
    ring

  have hderiv : deriv f 2 = 2 * 2 + m := by
    rw [hf]
    simp [deriv_pow, deriv_mul, deriv_id'', mul_comm m, add_left_comm]
    all_goals field_simp
  have hderiv_val : deriv f 2 = 4 + m := by
    rw [hderiv]
    ring

  rw [hderiv_val, hf2_val, hx1, hx2]
  all_goals ring