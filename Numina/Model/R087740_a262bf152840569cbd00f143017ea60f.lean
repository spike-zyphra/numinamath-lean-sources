import Mathlib

theorem inequalities_301673 (x : ℝ) :
    (∀ m ∈ Set.Icc (1 / 2) 3, x ^ 2 + m * x + 4 > 2 * m + 4 * x) ↔
    x > 2 ∨ x < -1 := by
  constructor
  · -- (∀ m ∈ Set.Icc (1 / 2) 3, x ^ 2 + m * x + 4 > 2 * m + 4 * x) → (x > 2 ∨ x < -1)
    intro h
    have h3 : x ^ 2 + 3 * x + 4 > 2 * 3 + 4 * x := by
      apply h 3
      norm_num
    have h1 : x ^ 2 + (1 / 2 : ℝ) * x + 4 > 2 * (1 / 2 : ℝ) + 4 * x := by
      apply h (1 / 2)
      norm_num
    by_cases h2 : x > 2
    · -- x > 2
      left
      exact h2
    · -- ¬(x > 2)
      have h2' : x ≤ 2 := by linarith
      have h4 : x < -1 := by
        nlinarith
      right
      linarith
  · -- (x > 2 ∨ x < -1) → (∀ m ∈ Set.Icc (1 / 2 3), x ^ 2 + m * x + 4 > 2 * m + 4 * x)
    rintro (h | h)
    · -- x > 2
      intro m hm
      rcases Set.mem_Icc.mp hm with ⟨hm1, hm2⟩
      nlinarith [sq_nonneg (x - 2), sq_nonneg (m - 3), sq_nonneg (m - 1 / 2), h, hm1, hm2]
    · -- x < -1
      intro m hm
      rcases Set.mem_Icc.mp hm with ⟨hm1, hm2⟩
      nlinarith [sq_nonneg (x - 2), sq_nonneg (m - 3), sq_nonneg (m - 1 / 2), h, hm1, hm2]