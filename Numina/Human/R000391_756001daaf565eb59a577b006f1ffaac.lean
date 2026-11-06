import Mathlib

/- Solve the inequality with respect to $x$: $(x-a)(x-a^2) < 0$ ($a \in \mathbb{R}$). -/
theorem algebra_9392 (a : ℝ) (x : ℝ) :
    (x - a) * (x - a ^ 2) < 0 ↔
    (a < 0 ∨ a > 1) ∧ a < x ∧ x < a ^ 2 ∨
    (0 < a ∧ a < 1) ∧ a ^ 2 < x ∧ x < a ∨
    (a = 0 ∨ a = 1) ∧ False := by

  -- (x - a)(x - a^2) < 0 <=> x - a < 0 and x - a^2 > 0 or x - a > 0 and x - a^2 < 0
  rw [mul_neg_iff]

  -- Split the goal into two
  constructor <;> intro h

  . -- case analysis
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h

    . left
      refine ⟨?_, by linarith, by linarith⟩

      -- a < x < a^2 forces a < 0 or a > 1
      have h : a * (1 - a) < 0 := by linarith
      rw [mul_neg_iff] at h
      obtain ⟨_, h3⟩ | ⟨h3, _⟩ := h
      . exact Or.inr (by linarith)
      . exact Or.inl (by linarith)

    . right; left
      refine ⟨?_, by linarith, by linarith⟩

      -- a^2 < x < a forces 0 < a < 1
      replace h : a * (a - 1) < 0 := by linarith
      rw [mul_neg_iff] at h
      obtain ⟨h3, h4⟩ | ⟨h3, h4⟩ := h
      . exact ⟨by linarith, by linarith⟩
      . linarith

  . simp at h

    -- case analysis
    obtain ⟨_, h2, h3⟩ | ⟨_, h2, h3⟩ := h
    . left
      exact ⟨by linarith, by linarith⟩
    . right
      exact ⟨by linarith, by linarith⟩
