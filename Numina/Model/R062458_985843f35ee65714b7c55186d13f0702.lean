import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_246575 : IsLeast {y | ∃ x, y = 2 * sin x - cos (2 * x)} (-3 / 2) ∧
    IsGreatest {y | ∃ x, y = 2 * sin x - cos (2 * x)} 3 := by
  constructor
  · -- Show -3/2 is the least value
    constructor
    · -- Show -3/2 exists
      use 7 * Real.pi / 6
      have hsin : sin (7 * Real.pi / 6) = -1 / 2 := by
        have h1 : sin (7 * Real.pi / 6) = sin (Real.pi + Real.pi / 6) := by
          ring_nf
          <;> simp [Real.pi_pos]
          <;> ring_nf
        rw [h1]
        rw [sin_add, sin_pi, cos_pi]
        have hsin' : sin (Real.pi / 6) = 1 / 2 := by
          exact sin_pi_div_six
        have hcos' : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
          exact cos_pi_div_six
        linarith [hsin', hcos']
      have hcos : cos (2 * (7 * Real.pi / 6)) = 1 / 2 := by
        have h1 : cos (2 * (7 * Real.pi / 6)) = cos (2 * Real.pi + Real.pi / 3) := by
          ring_nf
          <;> simp [Real.pi_pos]
          <;> ring_nf
        rw [h1]
        have h2 : cos (2 * Real.pi + Real.pi / 3) = cos (Real.pi / 3) := by
          have h3 : cos (2 * Real.pi + Real.pi / 3) = cos (Real.pi / 3 + 2 * Real.pi) := by 
            ring_nf
          rw [h3]
          rw [cos_add_two_pi]
        rw [h2]
        norm_num [cos_pi_div_three]
      linarith [hsin, hcos]
    · -- Show y >= -3/2
      intro y hy
      rcases hy with ⟨x, hx⟩
      have h1 : ∀ x : ℝ, 2 * sin x - cos (2 * x) = 2 * sin x ^ 2 + 2 * sin x - 1 := by
        intro x
        rw [cos_two_mul]
        rw [sin_sq]
        all_goals ring
      rw [h1 x] at hx
      have hsin : -1 ≤ sin x ∧ sin x ≤ 1 := by
        constructor
        · exact neg_one_le_sin x
        · exact sin_le_one x
      nlinarith [sq_nonneg (sin x + 1 / 2)]

  · -- Show 3 is the greatest value
    constructor
    · -- Show 3 exists
      use Real.pi / 2
      have hsin : sin (Real.pi / 2) = 1 := by 
        exact sin_pi_div_two
      have hcos : cos (2 * (Real.pi / 2)) = -1 := by 
        have h1 : 2 * (Real.pi / 2) = Real.pi := by 
          ring
          <;> simp
        rw [h1]
        norm_num [cos_pi]
      linarith [hsin, hcos]
    · -- Show y <= 3
      intro y hy
      rcases hy with ⟨x, hx⟩
      have h1 : ∀ x : ℝ, 2 * sin x - cos (2 * x) = 2 * sin x ^ 2 + 2 * sin x - 1 := by
        intro x
        rw [cos_two_mul]
        rw [sin_sq]
        all_goals ring
      rw [h1 x] at hx
      have hsin : -1 ≤ sin x ∧ sin x ≤ 1 := by
        constructor
        · exact neg_one_le_sin x
        · exact sin_le_one x
      nlinarith [sq_nonneg (sin x - 1)]