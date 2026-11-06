import Mathlib

theorem algebra_297788 (m : ℝ) (f : ℝ → ℝ)
    (hf : f = fun x => x^2 + (2 * m - 1) * x + m^2 - 2 * m + 1) :
    ∃! x, deriv f x = 1 ∧ f x = x := by
  use 1 - m
  constructor
  · -- First, check that $1 - m$ indeed satisfies both conditions
    constructor
    · -- Compute derivative at $1 - m$
      have hderiv : deriv f = fun x => 2 * x + (2 * m - 1) := by
        funext x
        rw [hf]
        simp [deriv_pow, deriv_add, deriv_mul, deriv_id'', mul_comm]
        all_goals field_simp
        <;> ring_nf <;> field_simp <;> ring
      rw [hderiv]
      simp
      ring
    · -- Now compute f(1 - m) and check if it equals 1 - m
      rw [hf]
      simp
      ring_nf
  · -- Now prove uniqueness. Suppose x satisfies both conditions, then x = 1 - m
    intro x
    intro hx
    rcases hx with ⟨hf1x, hfx⟩
    have hderiv : deriv f = fun x => 2 * x + (2 * m - 1) := by
      funext x
      rw [hf]
      simp [deriv_pow, deriv_add, deriv_mul, deriv_id'', mul_comm]
      all_goals field_simp
      <;> ring_nf <;> field_simp <;> ring
    have h1 : deriv f x = 1 := hf1x
    rw [hderiv] at h1
    simp at h1
    have hx : x = 1 - m := by
      linarith
    exact hx