import Mathlib
/-Find all pairs of nonnegative integers (x,y) for which (xy+2)^2=x^2+y^2-/
theorem algebra_71960 (x y : ℕ) :
    (x * y + 2) ^ 2 = x ^ 2 + y ^ 2 ↔ (x, y) = (0, 2) ∨ (x, y) = (2, 0) := by
  constructor
  · -- Assume (x * y + 2) ^ 2 = x ^ 2 + y ^ 2, we need to prove (x, y) = (0, 2) ∨ (x, y) = (2, 0)
    -- we observe that x and y can't be too large by the equation
    intro h
    have h1 : x ≤ 2 := by
      by_cases hx : x ≤ 2
      · linarith
      · -- Assume x > 2, we'll derive a contradiction
        push_neg at hx
        have h2 : x ≥ 3 := by linarith
        by_cases hy : y = 0
        · -- Case y = 0
          rw [hy] at h
          have : x = 2 := by
            nlinarith [h]
          linarith
        · -- Case y > 0
          replace hy : y ≥ 1 := by
            omega
          have h3 : (x * y + 2) ^ 2 > x ^ 2 + y ^ 2 := by     
            by_contra h'
            push_neg at h'
            have h6 : (x * y + 2) ^ 2 ≤ x ^ 2 + y ^ 2 := by linarith
            have h7 : x * y + 2 ≤ x + y := by nlinarith [h6, sq_nonneg (x * y), sq_nonneg (x + y)]
            nlinarith [mul_self_nonneg (x * y - 1), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1),
              h2, hy]
          nlinarith
    have h2 : y ≤ 2 := by -- similar to the case for x
      by_cases hy : y ≤ 2
      · linarith
      · -- Assume y > 2, we'll derive a contradiction
        push_neg at hy
        have h3 : y ≥ 3 := by linarith
        have h4 : (x * y + 2) ^ 2 > x ^ 2 + y ^ 2 := by
          interval_cases x <;> nlinarith [h3]
        nlinarith
    -- now x and y are both in [0, 2], we can check all cases
    interval_cases x <;> interval_cases y
    all_goals
      simp at h ⊢
  · -- now prove the reverse: if (x, y) = (0, 2) or (2, 0), then (x * y + 2) ^ 2 = x ^ 2 + y ^ 2
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Case (x, y) = (0, 2)
      norm_num
    · -- Case (x, y) = (2, 0)
      norm_num