import Mathlib

theorem algebra_143237 (m r : ℝ) (f : ℝ → ℝ) (hf : f = fun x => m * x + r * x - 2 * m + r + 1)
    (hparallel : ∀ x, deriv f x = -1) (hpoint : f 0 = 3) :
    m = -1 ∧ r = 0 := by

  have eq1 : f 0 = -2 * m + r + 1 := by
    rw [hf]
    norm_num
    <;> ring

  rw [eq1] at hpoint

  have h1 : deriv f 0 = -1 := hparallel 0

  have eq2 : deriv f 0 = m + r := by
    rw [hf]
    simp [deriv_const, deriv_id', deriv_add, deriv_mul, mul_comm m, mul_comm r]
    <;> ring
    <;> norm_num
    <;> ring

  rw [eq2] at h1

  have eq3 : m + r = -1 := by
    linarith [h1]

  have eq4 : -2 * m + r = 2 := by
    linarith [hpoint]

  have hm : m = -1 := by
    nlinarith [eq3, eq4]

  have hr : r = 0 := by
    linarith [hm, eq3]

  exact ⟨hm, hr⟩