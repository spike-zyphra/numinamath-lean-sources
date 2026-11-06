import Mathlib
/-Jasmine had 3 paperclips on Monday, then she had 6 on Tuesday, and her number of paperclips proceeded to double on each subsequent day. On what day of the week did she first have more than 100 paperclips?-/
theorem algebra_13519 : IsLeast {k | 3 * 2 ^ k > 100} 6 := by
  constructor
  · simp
  · intro a ha
    --  Thus, any term in this sequence can be represented as $3\cdot2^k$ for some non-negative integer $k$, where $k+1$ represents the term number. We need to find the smallest $k$ such that $3\cdot2^k>100$.
    simp at ha
    have : 2 ^ 5 < 2 ^ a := by nlinarith
    show 5 < a
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 <| this
