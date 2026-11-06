import Mathlib

/-- Which of the following numbers has the largest reciprocal?
(A) 1/3   (B) 2/5   (C) 1   (D) 5   (E) 1986 -/
theorem algebra_96380 {s : Set ℚ} (hs : s = {1/3, 2/5, 1, 5, 1986}):
    IsGreatest ((fun x ↦ 1 / x) '' s) (1 / (1/3)) := by

  -- We will show that 1/3 has the largest reciprocal.

  -- Because the reciprocal function is antitone, we can instead show that 1/3 is the smallest
  -- element in the set.
  suffices IsLeast s (1/3) from ?_
  · constructor
    · simp [hs]
    · rintro x ⟨q, hq, rfl⟩
      simp [hs] at hq
      rcases hq with (rfl | rfl | rfl | rfl | rfl) <;> norm_num

  -- We now show that 1/3 is the smallest element in the set.
  constructor
  -- 1/3 is in the set.
  · simp [hs]
  --1/3 is the smallest
  · simp [hs]; norm_num