import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21612 :
  -- 证明 17 是集合的最小元素
  -- 这个集合包含了函数 f(x) 的所有可能值
  IsLeast {x | ∃ t : ℝ, x = max (max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1))) (max (abs (t - 3)) (abs (t - 19)))} 17 := by 
  constructor
  · -- 证明 17 属于这个集合 
    use 2 
    norm_num [abs_of_pos, abs_of_neg]
    all_goals norm_num
  · -- 证明 17 是最小的 
    intro x hx 
    rcases hx with ⟨t, ht⟩ 
    by_contra h 
    push_neg at h 
    have h1 : max (max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1))) (max (abs (t - 3)) (abs (t - 19))) < (17 : ℝ) := by
      linarith [ht, h]
    by_cases h2 : t ≥ (2 : ℝ)
    · -- 当 t ≥ 2 时，|t + 15| ≥ 17
      have h5 : abs (t + 15) ≥ (17 : ℝ) := by 
        have h6 : t + 15 ≥ (17 : ℝ) := by linarith 
        have h7 : abs (t + 15) = t + 15 := by 
          rw [abs_of_nonneg (by linarith)]
        linarith [h7, h6]
      have h8 : max (abs (t + 15)) (abs (t + 12)) ≥ abs (t + 15) := by 
        apply le_max_left 
      have h9 : max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8)) ≥ max (abs (t + 15)) (abs (t + 12)) := by 
        apply le_max_left 
      have h10 : max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1)) ≥ max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8)) := by 
        apply le_max_left 
      have h11 : max (max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1))) (max (abs (t - 3)) (abs (t - 19))) ≥ max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1)) := by 
        apply le_max_left 
      linarith [h1, h5, h8, h9, h10, h11]
    · -- 当 t < 2 时，|t - 19| ≥ 17 
      have h6 : abs (t - 19) ≥ (17 : ℝ) := by 
        by_cases h8 : t - 19 ≥ 0 
        · -- t -19 ≥0 即 t≥19. 但此时t<2，矛盾 
          have h9 : t ≥ (19 : ℝ) := by linarith 
          linarith 
        · -- t -19 <0 即 t <19。此时abs(t-19) = 19-t.
          have h7 : abs (t - 19) = (19 - t) := by 
            rw [abs_of_neg (by linarith)]
            all_goals linarith 
          have h8 : (19 - t) ≥ (17 : ℝ) := by linarith 
          linarith [h7, h8]
      have h7 : max (abs (t - 3)) (abs (t - 19)) ≥ abs (t - 19) := by 
        apply le_max_right 
      have h8 : max (max (max (max (abs (t + 15)) (abs (t + 12))) (abs (t + 8))) (abs (t - 1))) (max (abs (t - 3)) (abs (t - 19))) ≥ max (abs (t - 3)) (abs (t - 19)) := by 
        apply le_max_right 
      linarith [h1, h6, h7, h8]