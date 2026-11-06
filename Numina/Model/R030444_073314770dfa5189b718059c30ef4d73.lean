import Mathlib

theorem algebra_12798 : {k : ℝ | ∀ x : ℝ, x^2 - (k - 3) * x - k + 6 > 0} = Set.Ioo (-3) 5 := by 
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume that ∀ x : ℝ, x^2 - (k - 3) * x - k + 6 > 0, prove k ∈ (-3, 5)
    intro h
    have h1 : ∀ x : ℝ, x ^ 2 - (k - 3) * x - k + 6 > 0 := h
    have h2 : k ^ 2 - 2 * k - 15 < 0 := by
      by_contra h3
      push_neg at h3
      have h3' : ( (k - 3) / 2 ) ^ 2 - (k - 3) * ( (k - 3) / 2 ) - k + 6 ≤ (0 : ℝ) := by
        nlinarith [sq_nonneg (k ^ 2 - 2 * k - 15), sq_nonneg (k - 3), sq_nonneg (k - 5), sq_nonneg (k + 3) ]
      have h4 : ( (k - 3) / 2 ) ^ 2 - (k - 3) * ( (k - 3) / 2 ) - k + 6 > 0 := by
        apply h1
        all_goals
          norm_num
          all_goals
            linarith
      linarith
    have h3 : k > -3 := by 
      nlinarith
    have h4 : k < 5 := by
      nlinarith
    constructor
    · exact h3
    · exact h4
  · -- Assume k ∈ (-3, 5), prove ∀ x : ℝ, x^2 - (k - 3) * x - k + 6 > 0
    rintro ⟨hk1, hk2⟩
    intro x
    have h2 : k ^ 2 - 2 * k - 15 < 0 := by
      nlinarith
    have h3 : x ^ 2 - (k - 3) * x - k + 6 > 0 := by
      nlinarith [sq_nonneg (x - (k - 3) / 2 ), sq_nonneg (k - 3), sq_nonneg (k - 5), sq_nonneg (k + 3) ]
    exact h3