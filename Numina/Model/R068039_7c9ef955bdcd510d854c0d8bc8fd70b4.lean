import Mathlib

theorem algebra_13316 (l1 l2 l3 : ℝ → ℝ → Prop)
    (hl1 : l1 = fun x y => 3 * y - 2 * x = 1)
    (hl2 : l2 = fun x y => x + 2 * y = 2)
    (hl3 : l3 = fun x y => 4 * x - 6 * y = 5) :
    {p : ℝ × ℝ | l1 p.1 p.2 ∧ l2 p.1 p.2 ∨ l1 p.1 p.2 ∧ l3 p.1 p.2 ∨
      l2 p.1 p.2 ∧ l3 p.1 p.2}.ncard = 2 := by
  have h1 : {p : ℝ × ℝ | l1 p.1 p.2 ∧ l2 p.1 p.2 ∨ l1 p.1 p.2 ∧ l3 p.1 p.2 ∨
      l2 p.1 p.2 ∧ l3 p.1 p.2} = {(4 / 7, 5 / 7), (11 / 7, 3 / 14)} := by
    ext ⟨x, y⟩
    simp [hl1, hl2, hl3]
    constructor
    · -- Assume (x, y) is on two lines, show it's one of the two points
      rintro (h | h | h)
      · -- Case where (x, y) is on both l1 and l2
        have h1 : 3 * y - 2 * x = 1 := h.1
        have h2 : x + 2 * y = 2 := h.2
        have hx : x = 4 / 7 := by
          linarith
        have hy : y = 5 / 7 := by
          linarith [h1, h2]
        left
        simp [hx, hy]
      · -- Case where (x, y) is on both l1 and l3
        have h1 : 3 * y - 2 * x = 1 := h.1
        have h3 : 4 * x - 6 * y = 5 := h.2
        exfalso
        linarith
      · -- Case where (x, y) is on both l2 and l3
        have h2 : x + 2 * y = 2 := h.1
        have h3 : 4 * x - 6 * y = 5 := h.2
        have hx : x = 11 / 7 := by
          linarith [h2, h3]
        have hy : y = 3 / 14 := by
          linarith [h2, h3]
        right
        simp [hx, hy]
    · -- Assume (x, y) is one of the two points, show it's on two lines
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Case where (4/7, 5/7)
        -- Show it's on both l1 and l2
        left
        constructor
        · -- On l1: 3 * (5/7) - 2 * (4/7) = 1
          norm_num
        · -- On l2: 4/7 + 2 * (5/7) = 2
          norm_num
      · -- Case where (11/7, 3/14)
        -- Show it's on both l2 and l3
        right
        right
        constructor
        · -- On l2: 11/7 + 2 * (3/14) = 2
          norm_num
        · -- On l3: 4 * (11/7) - 6 * (3/14) = 5
          norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num
  <;> norm_num
  all_goals linarith
  <;> norm_num
  all_goals linarith