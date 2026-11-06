import Mathlib
theorem algebra_608398 : IsLeast {a : ℝ | ∃ x : ℝ, a = x ^ 2 - 2 * x} (-1):= by
  constructor
  · -- Show that -1 is in the set.
    use 1
    norm_num
  · -- Show that -1 is the minimum in the set.
    intro a ha
    rcases ha with ⟨x, hx⟩
    have h : x ^ 2 - 2 * x ≥ -1 := by
      have h1 : (x - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
    linarith [hx, h]