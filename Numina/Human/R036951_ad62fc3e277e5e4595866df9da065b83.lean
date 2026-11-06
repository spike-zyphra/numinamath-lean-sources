import Mathlib

theorem algebra_9218 :
    IsLeast {n : ℕ | n > 0 ∧ ∃ k : ℤ, Real.sqrt (27 * n) = k} 3 := by

  -- We have two goals to prove:
  -- 1. 3 satisfies the condition
  -- 2. Any number less than 3 does not satisfy the condition
  constructor
  . -- Goal 1
    simp
    -- We prove that √27 * √3 = 9
    use 9
    -- Squaring both sides
    suffices _: (√27 * √3) ^ 2 = 9^2 by
      simp
      nlinarith [show √27 * √3 ≥ 0 by positivity]
    -- Simplify
    ring_nf
    norm_num
  . -- Goal 2
    simp only [lowerBounds, Set.mem_setOf]
    intro n ⟨hn, ⟨x, hx⟩⟩
    -- We need to prove that 1 and 2 do not satisfy the condition
    by_contra! h
    interval_cases n <;> clear * - hx

    . simp at hx
      have : √27 > 0 := by positivity
      -- 5 < √27 < 6
      have ⟨h1, h2⟩ : 5 < √27 ∧ √27 < 6 := by
        constructor <;>
        [(suffices _ : 5^2 < √27^2 by nlinarith);
         (suffices _ : √27^2 < 6^2 by nlinarith)] <;>
        norm_num
      -- 5 < x < 6
      replace ⟨h1, h2⟩ : (5 : ℝ) < x ∧ x < (6 : ℝ) := by constructor <;> linarith
      rw [show (5 : ℝ) = (5 : ℤ) by norm_num, Int.cast_lt] at h1
      rw [show (6 : ℝ) = (6 : ℤ) by norm_num, Int.cast_lt] at h2
      -- Impossible
      interval_cases x
    . norm_num at hx
      have : √54 > 0 := by positivity
      -- 7 < √54 < 8
      have ⟨h1, h2⟩ : 7 < √54 ∧ √54 < 8 := by
        constructor <;>
        [(suffices _ : 7^2 < √54^2 by nlinarith);
         (suffices _ : √54^2 < 8^2 by nlinarith)] <;>
        norm_num
      -- 7 < x < 8
      replace ⟨h1, h2⟩ : (7 : ℝ) < x ∧ x < (8 : ℝ) := by constructor <;> linarith
      rw [show (7 : ℝ) = (7 : ℤ) by norm_num, Int.cast_lt] at h1
      rw [show (8 : ℝ) = (8 : ℤ) by norm_num, Int.cast_lt] at h2
      -- Impossible
      interval_cases x
