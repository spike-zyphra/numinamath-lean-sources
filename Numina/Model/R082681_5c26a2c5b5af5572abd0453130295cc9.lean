import Mathlib

theorem algebra_326554 {a : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - 2 * a * x + a)
    (h : ∃ x, x < 1 ∧ f x = f 1) :
    ∀ x > 1, deriv (fun x => f x / x) x > 0 := by

  intro x hx

  have h1 : a < 1 := by 
    rcases h with ⟨y, hy1, hy2⟩
    have h_eq : f y = f 1 := by simpa using hy2
    have hy_eq : y ^ 2 - 2 * a * y + a = 1 ^ 2 - 2 * a * 1 + a := by
      rw [hf y, hf 1] at h_eq
      linarith
    have h_eq'' : y^2 - 2 * a * y + 2 * a - 1 = 0 := by
      linarith
    nlinarith [sq_nonneg (y - 1), sq_nonneg (a - 1), sq_nonneg (x - 1)]

  have h2 : deriv (fun x => f x / x) x = (x ^ 2 - a) / x ^ 2 := by
    simp [hf, deriv_div, deriv_pow, deriv_add, deriv_sub, deriv_mul, mul_comm, mul_assoc]
    all_goals field_simp <;> ring_nf <;> field_simp <;> ring
    <;> field_simp <;> nlinarith

  have h3 : deriv (fun x => f x / x) x > 0 := by
    rw [h2]
    have hx2_pos : 0 < x ^ 2 := by
      nlinarith
    have h4 : x ^ 2 - a > 0 := by
      nlinarith [sq_pos_of_pos (show x > 0 by linarith), h1]
    apply div_pos
    exact h4
    exact hx2_pos

  exact h3