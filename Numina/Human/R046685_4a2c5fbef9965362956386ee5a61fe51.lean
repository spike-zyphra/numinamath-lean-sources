import Mathlib

theorem algebra_248630 (x y z : ℝ) :
    x + y = z ∧ x^2 + y^2 = z ∧ x^3 + y^3 = z ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 2) := by
  constructor
  · -- Assume the equations hold, we need to prove the disjunction
    rintro ⟨h1, h2, h3⟩
    have h4 : z = x + y := by linarith
    rw [h4] at h2 h3
    have h5 : x^3 + y^3 = x + y := by linarith
    have h6 : (x + y) * (x^2 - x * y + y^2) = x + y := by
      nlinarith [h5]
    by_cases h : x + y = 0
    · -- Case x + y = 0
      have hz : z = 0 := by linarith [h4]
      have hx : x = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), h]
      have hy : y = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y), h]
      left
      exact ⟨hx, hy, hz⟩
    · -- Case x + y ≠ 0
      have h7 : x^2 - x * y + y^2 = 1 := by
        have hne : x + y ≠ 0 := by
          intro h0
          apply h
          linarith
        have eq1 : (x + y) * (x^2 - x * y + y^2) = x + y := by linarith
        have : x^2 - x * y + y^2 = 1 := by
          apply (mul_left_inj' hne).mp
          linarith
        assumption
      have h8 : x * y = x + y - 1 := by
        nlinarith [sq_nonneg (x - y), h7, h2]
      have h9 : (x - 1) * (y - 1) = 0 := by
        nlinarith [h8]
      cases' (mul_eq_zero.mp h9) with hx1 hy1
      · -- x - 1 = 0, so x = 1
        have hx_eq_1 : x = 1 := by linarith
        have hy_eq_0_or_1 : y = 0 ∨ y = 1 := by
          have h : y^2 = y := by
            nlinarith [h2, hx_eq_1]
          have : y * (y - 1) = 0 := by linarith
          cases' (mul_eq_zero.mp this) with hy0 hy1
          · -- y = 0
            left
            linarith
          · -- y - 1 = 0, so y = 1
            right
            linarith
        cases' hy_eq_0_or_1 with hy0 hy1
        · -- y = 0
          have hz_eq_1 : z = 1 := by
            rw [hx_eq_1, hy0] at h4
            linarith
          right
          right
          left
          exact ⟨hx_eq_1, hy0, hz_eq_1⟩
        · -- y = 1
          have hz_eq_2 : z = 2 := by
            rw [hx_eq_1, hy1] at h4
            linarith
          right
          right
          right
          exact ⟨hx_eq_1, hy1, hz_eq_2⟩
      · -- y - 1 = 0, so y = 1
        have hy_eq_1 : y = 1 := by linarith
        have hx_eq_0_or_1 : x = 0 ∨ x = 1 := by
          have h : x^2 = x := by
            nlinarith [h2, hy_eq_1]
          have : x * (x - 1) = 0 := by linarith
          cases' (mul_eq_zero.mp this) with hx0 hx1
          · -- x = 0
            left
            linarith
          · -- x - 1 = 0, so x = 1
            right
            linarith
        cases' hx_eq_0_or_1 with hx0 hx1
        · -- x = 0
          have hz_eq_1 : z = 1 := by
            rw [hx0, hy_eq_1] at h4
            linarith
          right
          left
          exact ⟨hx0, hy_eq_1, hz_eq_1⟩
        · -- x = 1
          have hz_eq_2 : z = 2 := by
            rw [hx1, hy_eq_1] at h4
            linarith
          right
          right
          right
          exact ⟨hx1, hy_eq_1, hz_eq_2⟩
  · -- Now prove the reverse direction
    rintro (h | h | h | h)
    · -- (0,0,0)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- x + y = z
        norm_num
      constructor
      · -- x^2 + y^2 = z
        norm_num
      · -- x^3 + y^3 = z
        norm_num
    · -- (0,1,1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- x + y = z
        norm_num
      constructor
      · -- x^2 + y^2 = z
        norm_num
      · -- x^3 + y^3 = z
        norm_num
    · -- (1,0,1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- x + y = z
        norm_num
      constructor
      · -- x^2 + y^2 = z
        norm_num
      · -- x^3 + y^3 = z
        norm_num
    · -- (1,1,2)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- x + y = z
        norm_num
      constructor
      · -- x^2 + y^2 = z
        norm_num
      · -- x^3 + y^3 = z
        norm_num