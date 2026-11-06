import Mathlib

theorem algebra_2232 {x : ℝ} (hx : x ≠ 1) (h : 1 / (x - 1) - 2 / (x ^ 2 - 1) = 1 / 3) :
    x = 2 := by
  have h1 : x ^ 2 - 1 ≠ 0 := by
    by_contra h2
    have h3 : (x - 1) * (x + 1) = 0 := by linarith [h2]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case $x - 1 = 0$, so $x = 1$
      exfalso
      exact hx (by linarith)
    · -- Case $x + 1 = 0$, so $x = -1$
      have h6 : x = -1 := by linarith
      rw [h6] at h
      norm_num at h
  have h2 : x - 1 ≠ 0 := by
    intro h3
    apply hx
    linarith
  have h3 : x + 1 ≠ 0 := by
    intro h4
    have h5 : x ^ 2 - 1 = 0 := by
      have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
      rw [this]
      rw [h4]
      ring_nf
    contradiction
  have eq1 : (1 / (x - 1) - 2 / (x ^ 2 - 1)) * (x ^ 2 - 1) = (1 / 3) * (x ^ 2 - 1) := by
    rw [h]
  have eq2 : (1 / (x - 1) - 2 / (x ^ 2 - 1)) * (x ^ 2 - 1) = x - 1 := by
    field_simp [(show x - 1 ≠ 0 by simpa using h2), (show x ^ 2 - 1 ≠ 0 by simpa using h1), (show x + 1 ≠ 0 by simpa using h3)] at *
    ring_nf
  have eq4 : x - 1 = (1 / 3) * (x ^ 2 - 1) := by
    linarith [eq1, eq2]
  have eq5 : 3 * (x - 1) = x^2 - 1 := by
    nlinarith [eq4]
  have eq6 : x^2 - 3 * x + 2 = 0 := by
    nlinarith [eq5]
  have eq7 : (x - 1) * (x - 2) = 0 := by
    nlinarith [eq6]
  cases' (mul_eq_zero.1 eq7) with h7 h8
  · -- Case $x - 1 = 0$, so $x = 1$, which contradicts with the hypothesis hx.
    exfalso
    have h9 : x = 1 := by linarith
    contradiction
  · -- Case $x - 2 = 0$, so $x = 2$.
    linarith