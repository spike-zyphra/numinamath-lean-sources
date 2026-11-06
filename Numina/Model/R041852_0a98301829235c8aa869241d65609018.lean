import Mathlib
theorem algebra_610632 : {(x, y, z) : ℝ × ℝ × ℝ | x * y + z = 40 ∧ x * z + y = 51 ∧ x + y + z = 19} = {(12, 3, 4), (6, 5.4, 7.6)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First direction: if (x, y, z) satisfy the three equations, then it's either (12, 3, 4) or (6, 5.4, 7.6)
    rintro ⟨h₁, h₂, h₃⟩
    have h₄ : z = 19 - x - y := by linarith
    rw [h₄] at h₁ h₂
    have h₅ : x * y - x - y = 21 := by
      nlinarith
    have h₆ : -x ^ 2 + 18 * x = 72 := by
      nlinarith [h₁, h₂, h₅]
    have h₇ : (x - 6) * (x - 12) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h₇) with h₈ h₉
    · -- Case h₈: x - 6 = 0, so x = 6.
      have hx : x = 6 := by linarith
      have hy : y = 5.4 := by
        have h₅' : x * y - x - y = 21 := by
          linarith
        rw [hx] at h₅'
        norm_num at h₅' ⊢
        linarith
      have hz : z = 7.6 := by
        have h₄' : z = 19 - x - y := by
          linarith
        rw [hx, hy] at h₄'
        norm_num at h₄' ⊢
        linarith
      right
      simp [hx, hy, hz]
      all_goals nlinarith
    · -- Case h₉: x - 12 = 0, so x = 12.
      have hx : x = 12 := by linarith
      have hy : y = 3 := by
        have h₅' : x * y - x - y = 21 := by
          linarith
        rw [hx] at h₅'
        linarith
      have hz : z = 4 := by
        have h₄' : z = 19 - x - y := by
          linarith
        rw [hx, hy] at h₄'
        linarith
      left
      simp [hx, hy, hz]
      all_goals nlinarith
  · -- Now the reverse direction: both solutions satisfy the three equations.
    rintro (h | h)
    · -- Case (12, 3, 4)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (6, 5.4, 7.6)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num