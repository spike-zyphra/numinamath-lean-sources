import Mathlib

theorem algebra_14054 : {x : ℝ | -25 * x < x ^ 3 - 10 * x ^ 2} = Set.Ioo 0 5 ∪ Set.Ioi 5 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · -- Assume $-25x < x^3 - 10x^2$ holds, prove $x \in (0,5) \cup (5, \infty)$
    intro h
    have h1 : x ^ 3 - 10 * x ^ 2 + 25 * x > 0 := by linarith
    have h2 : x * (x - 5) ^ 2 > 0 := by nlinarith
    have h3 : x > 0 := by
      nlinarith [sq_nonneg (x - 5)]
    have h4 : x ≠ 5 := by
      by_contra h'
      have : x = 5 := by linarith
      rw [this] at h2
      nlinarith
    by_cases h5 : x < 5
    · -- Case 1: x < 5, so x ∈ (0,5)
      left
      constructor
      · linarith
      · linarith
    · -- Case 2: x ≥ 5
      have h6 : x ≥ 5 := by linarith
      have h7 : x > 5 := by
        by_contra h8
        push_neg at h8
        have : x = 5 := by linarith
        contradiction
      right
      linarith
  · -- Assume x ∈ (0,5) ∪ (5, ∞), prove -25 * x < x ^ 3 - 10 * x ^ 2
    rintro (h | h)
    · -- Case 1: x ∈ (0,5)
      rcases h with ⟨hx1, hx2⟩
      have h1 : x ^ 3 - 10 * x ^ 2 + 25 * x > 0 := by
        have h2 : x * (x - 5) ^ 2 > 0 := by
          have hx3 : x - 5 < 0 := by linarith
          nlinarith [sq_pos_of_neg hx3, sq_nonneg (x - 5)]
        nlinarith
      linarith
    · -- Case 2: x ∈ (5, ∞)
      have hx1 : x > 5 := h
      have h1 : x ^ 3 - 10 * x ^ 2 + 25 * x > 0 := by
        have h2 : x * (x - 5) ^ 2 > 0 := by
          have hx2 : x - 5 > 0 := by nlinarith
          nlinarith [sq_pos_of_pos hx2, sq_nonneg (x - 5)]
        nlinarith
      linarith