import Mathlib

/- 8. [7] Let $a, b, c$ be not necessarily distinct integers between 1 and 2011, inclusive. Find the smallest possible value of $\frac{a b+c}{a+b+c}$. -/
theorem algebra_160634 :
    IsLeast {x : ℚ | ∃ a b c : ℤ, x = (a * b + c) / (a + b + c) ∧ 1 ≤ a ∧ a ≤ 2011 ∧ 1 ≤ b ∧ b ≤ 2011 ∧ 1 ≤ c ∧ c ≤ 2011} (2 / 3) := by
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Show that the value 2 / 3 is achievable when a = b = c = 1.
  · use 1, 1, 1
    norm_num
  -- Show that 2 / 3 ≤ (a * b + c) / (a + b + c) for any integers a, b, c ∈ [1, 2011].
  intro x a b c hx ha1 ha2 hb1 hb2 hc1 hc2
  -- Rewrite the inequality as 3 * (a + b + c) ≤ (a * b + c) * 3.
  rw [hx, div_le_div_iff₀ (by norm_num) (by norm_cast; omega)]
  norm_cast
  -- nlinarith can solve the remaining goal. Consider a more detailed proof.
  calc
    -- 2 * (a + b + c) ≤ 2 * (a + b + c) + 3 * (a - 1) * (b - 1) + ((a + b + c) - 3)
    --   = (a * b + c) * 3.
    2 * (a + b + c) = 2 * (a + b + c) + 3 * 0 * 0 + 0 := by norm_num
    _ ≤ 2 * (a + b + c) + 3 * (a - 1) * (b - 1) + ((a + b + c) - 3) := by gcongr <;> linarith
    _ = (a * b + c) * 3 := by ring