import Mathlib

theorem algebra_190657 (a b : ℕ) :
    (a + 6) * (b + 5) = 3 * a * b ↔
    (a = 48 ∧ b = 3) ∨
    (a = 18 ∧ b = 4) ∨
    (a = 12 ∧ b = 5) ∨
    (a = 8 ∧ b = 7) ∨
    (a = 6 ∧ b = 10) ∨
    (a = 4 ∧ b = 25) := by 
  constructor
  · -- Assume (a + 6) * (b + 5) = 3 * a * b, prove the disjunction of the pairs
    intro h
    have eq1 : a * b + 5 * a + 6 * b + 30 = 3 * a * b := by
      nlinarith
    have eq2 : 2 * a * b = 5 * a + 6 * b + 30 := by
      nlinarith [eq1]

    have h1 : a ≤ 48 := by
      by_contra h2
      push_neg at h2
      have h3 : b ≤ 25 := by
        nlinarith [sq_nonneg (a * 2 - 5 * b), sq_nonneg (b - 3), sq_nonneg (a - 48), sq_nonneg (b - 25)]
      interval_cases b <;> omega

    have h2 : b ≤ 25 := by
      by_contra h2
      push_neg at h2
      have h3 : a ≤ 5 := by
        nlinarith [sq_nonneg (b * 2 - 5 * a), sq_nonneg (a - 5), sq_nonneg (b * 2 - 45), sq_nonneg (a - 48)]
      interval_cases a <;> omega

    interval_cases a <;> omega
  · -- Assume the disjunction of the pairs, prove (a + 6) * (b + 5) = 3 * a * b
    rintro (h | h | h | h | h | h)
    · -- First pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Second pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Third pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Fourth pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Fifth pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Sixth pair
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num