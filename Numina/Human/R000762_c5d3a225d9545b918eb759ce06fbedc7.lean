import Mathlib

/- Anthony made $5$ of his first $12$ free throw attempts. If he makes $2/3$ of his next $24$ attempts, by how many percentage points will he increase his overall success rate percentage? Express your answer to the nearest whole number. -/
theorem algebra_14887 (m₁ n₁ m₂ n₂ : ℕ) (h₁ : m₁ = 5) (h₂ : n₁ = 12) (h₃ : (m₂ : ℚ) = 2 / 3 * n₂) (h₄ : n₂ = 24) :
    round ((m₁ + m₂) / (n₁ + n₂) * 100 - m₁ / n₁ * 100 : ℚ) = 17 := by
  subst_vars
  norm_num at h₃
  norm_cast at h₃
  subst h₃
  norm_num [round_eq]
