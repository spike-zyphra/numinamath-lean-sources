import Mathlib

theorem algebra_9064 (m : ℝ) :
    (∀ a b : ℝ, (a > 0 ∧ b > 0 ∧ a * b = a + b + 3) → a * b ≥ m) ↔ m ≤ 9 := by
  constructor
  · -- First, we show that if `∀ a b : ℝ, (a > 0 ∧ b > 0 ∧ a * b = a + b + 3) → a * b ≥ m`, then $m \leq 9$.
    intro h
    have h3 := h 3 3 (by norm_num)
    nlinarith
  · -- Now, we show the reverse: if $m \leq 9$, then `∀ a b : ℝ, (a > 0 ∧ b > 0 ∧ a * b = a + b + 3) → a * b ≥ m`.
    intro hm a b h
    rcases h with ⟨ha, hb, hab⟩
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (a - b), mul_pos ha hb]