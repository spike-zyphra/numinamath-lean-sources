import Mathlib

theorem algebra_227527 (a : ℝ) (ha : a ≠ 0) (h : ∃ x : ℝ, a * (1 + Complex.I) * x^2 + (1 + a^2 * Complex.I) * x + a^2 + Complex.I = 0) :
    a = -1 := by
  rcases h with ⟨x, hx⟩
  simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc] at hx
  have h1 := hx.1
  have h2 := hx.2
  have h3 : a * x^2 = -x - a^2 := by linarith
  have h4 : (-x - a^2) + a^2 * x + 1 = 0 := by linarith
  have h5 : (a^2 - 1) * (x - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where $a^2 - 1 = 0$ implies $a = \pm 1$.
    have h8 : a^2 = 1 := by nlinarith
    have h9 : a = 1 ∨ a = -1 := by
      rw [sq_eq_one_iff] at h8
      exact h8
    cases' h9 with ha1 ha2
    · -- Let's verify if $a = 1$ is consistent with our real solution equations.
      have ha1' : a = 1 := ha1
      rw [ha1'] at h1
      nlinarith [sq_nonneg (x + 1/2)]
    · -- $a = -1$ is our desired solution.
      have ha2' : a = -1 := ha2
      linarith
  · -- Case where $x = 1$.
    have h8 : x = 1 := by linarith
    rw [h8] at h1
    nlinarith [sq_nonneg (a + 1/2)]