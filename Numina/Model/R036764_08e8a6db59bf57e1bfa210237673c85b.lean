import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem inequalities_262738 (r : ℝ) :
  (∀ a b : ℝ, a ≥ r → b ≥ r → a^3 + a * b + b^3 ≥ a^2 + b^2) ↔
  r ≥ 1 / 2 := by
  constructor
  · -- Forward direction: if ∀ a b ≥ r, a^3 + ab + b^3 ≥ a^2 + b^2, then r ≥ 1/2.
    intro h
    by_contra h1
    push_neg at h1
    -- We need to show that if r < 1/2, we can find a counterexample.
    have h2 : r < 1 / 2 := by linarith
    -- Let's take a = 1/2 and b = r.
    -- Then $a \geq r$ and $b \geq r$ because $1/2 \geq r$ and $r \geq r$.
    have h3 := h (1 / 2 : ℝ) (r : ℝ) (by nlinarith) (by nlinarith)
    -- The inequality becomes: $(1/2)^3 + (1/2)(r) + r^3 \geq (1/2)^2 + r^2$.
    -- Multiply through by 8 to clear denominators:
    -- $1 + 4r + 8r^3 \geq 2 + 8r^2$
    -- Rearrange:
    -- $8r^3 - 8r^2 + 4r - 1 \geq 0$.
    -- Factor this as $(r - 1/2)(8r^2 - 4r + 2) \geq 0$.
    -- Since r < 1/2, so r - 1/2 < 0.
    -- And $8r^2 - 4r + 2$ is always positive.
    -- So the entire expression is negative, contradicting the inequality.
    nlinarith [sq_nonneg (r - 1 / 2), sq_nonneg (r + 1 / 2), sq_nonneg ((1 / 2 : ℝ) - r), sq_nonneg ((1 / 2 : ℝ) ^ 2 - r ^ 2), sq_nonneg (r ^ 2 - (1 / 2 : ℝ) ^ 2) ]
  · -- Backward direction: if r ≥ 1/2, then ∀ a b ≥ r, a^3 + ab + b^3 ≥ a^2 + b^2.
    intro hr a b ha hb
    have ha2 : a ≥ 1 / 2 := by linarith
    have hb2 : b ≥ 1 / 2 := by linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1),
        mul_nonneg (show 0 ≤ a - 1 / 2 by linarith) (show 0 ≤ b - 1 / 2 by linarith)
      ]