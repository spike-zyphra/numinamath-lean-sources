import Mathlib

theorem algebra_21399 {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 - 8) :
    f ⁻¹' {19} = {3} := by
  ext x
  simp [hf]
  constructor
  · -- Assume $x^3 - 8 = 19$, prove $x = 3$
    intro h
    have h1 : x ^ 3 = 27 := by linarith
    have h2 : x = 3 := by
      have h3 : x ^ 3 - 27 = 0 := by linarith
      have h4 : x ^ 3 - 27 = (x - 3) * (x ^ 2 + 3 * x + 9) := by
        ring
      rw [h4] at h3
      cases' (mul_eq_zero.1 h3) with h5 h6
      · linarith
      · -- Case $x^2 + 3x + 9 = 0$
        have h7 : x ^ 2 + 3 * x + 9 > 0 := by
          nlinarith [sq_nonneg (x + 3 / 2)]
        have h8 : x ^ 2 + 3 * x + 9 ≠ 0 := by
          nlinarith [h7]
        exfalso
        exact h8 h6
    exact h2
  · -- Assume $x = 3$, prove $x^3 - 8 = 19$
    intro h
    rw [h]
    norm_num