import Mathlib

/- Natural numbers $k, l,p$ and $q$ are such that if $a$ and $b$ are roots of $x^2 - kx + l = 0$ then $a +\frac1b$ and $b + \frac1a$ are the roots of $x^2 -px + q = 0$. What is the sum of all possible values of $q$? -/

theorem algebra_75217 (k l p q : ℕ) 
  (hab : ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a + b = k ∧ a * b = l):
  (∀ a b : ℝ, (∀ x, x^2 - k * x + l = (x-a) * (x-b)) → a ≠ 0 → b ≠ 0 →
  (∀ x, x^2 - p * x + q = (x - (a + 1 / b)) * (x - (b + 1 / a))))
  → q = 4 := by

  intro h
  rcases hab with ⟨a, b, ha, hb, hk, hl⟩
  have : ∀ (x : ℝ), x ^ 2 - ↑k * x + ↑l = (x - a) * (x - b) := by
    intro x
    rw [← hk, ← hl]
    ring_nf

  have := h a b this ha hb 0
  simp at this
  ring_nf at this
  field_simp at this
  rw [show b * a = l by linarith] at this
  norm_cast at this
  have h1 : l ≤ 3 := by
    by_contra h2
    push_neg at h2
    have h2' : l ≥ 4 := by omega
    have h3 : q ≥ l + 3 := by
      nlinarith
    have h4 : q < l + 3 := by
      nlinarith
    omega
  interval_cases l <;> omega
