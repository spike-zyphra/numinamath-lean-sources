import Mathlib

theorem algebra_200463 (p : ℝ) :
    (∃ x y : ℝ, 2 * ⌊x⌋ + y = 3 / 2 ∧ 3 * ⌊x⌋ - 2 * y = p) ↔
    ∃ k : ℤ, p = 7 * k - 3 := by
  constructor
  · -- Assume there exist x, y satisfying the system, prove ∃ k : ℤ, p = 7 * k - 3
    rintro ⟨x, y, h1, h2⟩
    have eq1 : y = 3 / 2 - 2 * (⌊x⌋ : ℝ) := by linarith
    rw [eq1] at h2
    have hp : p = 7 * (⌊x⌋ : ℝ) - 3 := by linarith
    refine ⟨⌊x⌋, by
      rw [hp]
      all_goals norm_num
    ⟩
  · -- Assume ∃ k : ℤ, p = 7 * k - 3, prove there exist x, y satisfying the system
    rintro ⟨k, hk⟩
    use (k : ℝ)
    use (3 / 2 - 2 * (k : ℝ))
    constructor
    · -- Verify the first equation: 2 * ⌊k⌋ + (3 / 2 - 2 * k) = 3 / 2
      have h1 : ⌊((k : ℝ) : ℝ)⌋ = k := by
        simp
      rw [h1]
      all_goals norm_num
    · -- Verify the second equation: 3 * ⌊k⌋ - 2 * (3 / 2 - 2 * k) = p
      have h1 : ⌊((k : ℝ) : ℝ)⌋ = k := by
        simp
      rw [h1]
      rw [hk]
      all_goals norm_num
      <;> ring