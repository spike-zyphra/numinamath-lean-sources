import Mathlib

/-The solution set of the inequality $2x^2 - 3x - 2 > 0$ is ______.-/
theorem algebra_9323 (x : ℝ) :
    2 * x ^ 2 - 3 * x - 2 > 0 ↔ x < -1 / 2 ∨ x > 2 := by
      constructor <;> intro h
      · -- To solve the inequality $2x^2 - 3x - 2 > 0$, we can factor it as follows:
        -- $$(2x + 1)(x - 2) > 0$$
        have : 2 * x ^ 2 - 3 * x - 2 = (2 * x + 1) * (x - 2) := by nlinarith
        rw [this] at h
        -- So $(2 * x + 1)$ and $x - 2$ have same parity.
        rcases  mul_pos_iff.1 h  with h1 | h2
        · -- when both $(2 * x + 1)$ and $x - 2$ positive, $x > 2$.
          right; linarith
        · -- when both $(2 * x + 1)$ and $x - 2$ negative, $x < -1 / 2$.
          left; linarith
      · -- Verify when $x < -1 / 2$ or $x > 2$, $2 * x ^ 2 - 3 * x - 2 > 0$.
        rcases h with h | h <;> nlinarith
