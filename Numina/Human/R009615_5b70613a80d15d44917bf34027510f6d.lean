import Mathlib

/-Determine the range of the real number $a$ such that the inequality $x^2 - ax + a > 0$ is always satisfied.-/
theorem algebra_9454 (a : ℝ) :
  (∀ x : ℝ, x^2 - a * x + a > 0) ↔ 0 < a ∧ a < 4 := by
    constructor <;> intro h
    · -- when $x = a / 2$, the quadratic $x^2 - a * x + a$ get the minimum.
      -- So if the minimum is postive, for any real number $x$, $x^2 - a * x + a > 0$ holds true.
      specialize h (a / 2)
      ring_nf at h
      nth_rw 1 [←mul_one a] at h
      rw [pow_two, mul_assoc, ←mul_add] at h
      rcases mul_pos_iff.1 h with hl | hr <;> try linarith
      exact ⟨hl.1, by linarith⟩
    · -- $x^2 - a * x + a = (x - a / 2)^2 - a^2 / 4 + a$, $(x - a / 2)^2$ is always nonneg,
      -- so just vertfy $- a^2 / 4 + a$ is positive.
      intro x
      have : x^2 - a * x + a = (x - a / 2)^2 - a^2 / 4 + a := by nlinarith
      rw [this]
      nlinarith
