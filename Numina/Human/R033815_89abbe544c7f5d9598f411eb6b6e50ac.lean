import Mathlib

/- If $a$ and $b$ are integers with $a > b$, what is the smallest possible positive value of $\frac{a+b}{a-b} + \frac{a-b}{a+b}$? -/
theorem algebra_12907 :
    IsLeast {x : ℝ | ∃ a b : ℤ, a > b ∧ x > 0 ∧ x = (a + b) / (a - b) + (a - b) / (a + b)} 2 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- The minimum value is achievable by setting a = 1, b = 0.
    use 1
    use 0
    norm_num
  . -- The value 2 is a lower bound to (a + b) / (a - b) + (a - b) / (a + b).
    intro x a b _ xpos hx
    let y : ℝ := (a + b) / (a - b)
    simp [show (a + b) / (a - b) = y by dsimp [y], show (a - b) / (a + b) = 1 / y by rw [<-one_div_div], -one_div] at hx
    have h : 0 ≤ (Real.sqrt y - Real.sqrt (1 / y)) ^ 2 := by
      positivity
    rw [hx]
    replace h : 2 * Real.sqrt y * Real.sqrt (1 / y) ≤ Real.sqrt y ^ 2 + Real.sqrt (1 / y) ^ 2 := by
      linarith only [h]
    rw [mul_assoc, <-Real.sqrt_mul, mul_one_div_cancel, Real.sq_sqrt, Real.sq_sqrt] at h
    norm_num at h ⊢
    exact h
    simp
    all_goals try
      -- If y is negative, then x is negative, contradicting our assumption.
      by_contra! yneg
      absurd hx
      simp [<-ne_eq, <-lt_or_lt_iff_ne, -one_div]
      right
      calc
        y + 1 / y < 0 + 0 := by apply add_lt_add; exact yneg; simp; exact yneg
        _ < x := by norm_num; exact xpos
    by_contra! hy
    rw [hy] at hx
    simp at hx
    rw [hx] at xpos
    linarith only [xpos]
