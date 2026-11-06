import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_210093 (s : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, s x y = min (min x (1 - y)) (y - x)) :
  IsGreatest {z | ∃ x y, z = s x y} (1 / 3) := by
  constructor 
  · -- Show that 1/3 is in the set
    use 1 / 3, 2 / 3 
    rw [h₀]
    norm_num 
    all_goals norm_num 
  · -- Show it's greatest
    intro z hz 
    rcases hz with ⟨x, y, hz⟩ 
    rw [h₀] at hz 
    by_contra h1 
    push_neg at h1 
    have h21 : min (min x (1 - y)) (y - x) ≤ x := by
      have h24 : min x (1 - y) ≤ x := by
        cases' min_cases x (1 - y) with h25 h25 
        · -- Case where min x (1-y) = x
          linarith 
        · -- Case where min x (1-y) = 1-y 
          linarith 
      cases' min_cases (min x (1 - y)) (y - x) with h23 h23 
      · -- Case where min (min x (1-y)) (y-x) = min x (1-y) 
        linarith [h24, h23.1] 
      · -- Case where min (min x (1-y)) (y-x) = y-x 
        all_goals 
          linarith 
    -- Show that s(x, y) ≤ 1 - y
    have h21' : min (min x (1 - y)) (y - x) ≤ 1 - y := by 
      have h24' : min x (1 - y) ≤ 1 - y := by 
        cases' min_cases x (1 - y) with h25 h25 
        · -- Case where min x (1-y) = x 
          linarith 
        · --  Case where min x (1-y) = 1-y 
          linarith 
      cases' min_cases (min x (1 - y)) (y - x) with h23 h23 
      · -- Case where min (min x (1-y)) (y-x) = min x (1-y) 
        linarith [h24', h23.1] 
      · -- Case where min (min x (1-y)) (y-x) = y-x 
        all_goals
          linarith 
    -- Show that s(x, y) ≤ y - x
    have h21'' : min (min x (1 - y)) (y - x) ≤ y - x := by
      cases' min_cases (min x (1 - y)) (y - x) with h23 h23 
      · -- Case where min (min x (1-y)) (y-x) = min x (1-y) 
        cases' min_cases x (1 - y) with h19 h19 
        all_goals 
          linarith 
      · -- Case where min (min x (1-y)) (y-x) = y-x 
        all_goals 
          linarith 
    -- Now we can derive the conditions
    -- Substituting z in h1
    have h31 : x > 1 / 3 := by
      by_contra h31
      push_neg at h31 
      nlinarith [hz, h1, h21, h31]
    -- Substituting z in h1
    have h32 : y < 2 / 3 := by
      by_contra h32
      push_neg at h32 
      nlinarith [hz, h1, h21', h32]
    -- Substituting z in h1
    have h33 : y > x + 1 / 3 := by 
      by_contra h33
      push_neg at h33 
      nlinarith [hz, h1, h21'', h33]
    -- Now deriving the contradiction 
    nlinarith [h31, h33, h32]