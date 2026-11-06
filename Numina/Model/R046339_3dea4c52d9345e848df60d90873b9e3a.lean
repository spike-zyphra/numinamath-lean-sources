import Mathlib

theorem algebra_9369 {f : ℝ → ℝ} (hf : f = fun x => x * (x + k) * (x + 2 * k) * (x - 3 * k)) (h : deriv f 0 = 6) :
    k = -1 := by
  have eq1 : deriv f 0 = -6 * k ^ 3 := by
    rw [hf]
    simp [deriv_mul, deriv_id'', deriv_const, mul_comm]
    norm_num
    <;> ring_nf <;> field_simp
    <;> ring
  rw [eq1] at h
  have eq2 : -6 * k ^ 3 = 6 := by linarith
  have eq3 : k ^ 3 = -1 := by
    nlinarith
  have eq4 : k = -1 := by
    have h1 : k ^ 3 + 1 = 0 := by linarith
    have h2 : (k + 1) * (k ^ 2 - k + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case where k + 1 = 0
      linarith
    · -- Case where k ^ 2 - k + 1 = 0
      have h5 : k ^ 2 - k + 1 > 0 := by
        nlinarith [sq_nonneg (k - 1 / 2)]
      nlinarith
  exact eq4