import Mathlib

theorem algebra_93186 :
    {(x, y) : ℝ × ℝ | x = x ^ 2 + y ^ 2 ∧ y = 2 * x * y}.encard = 4 := by
  have h : {(x, y) : ℝ × ℝ | x = x ^ 2 + y ^ 2 ∧ y = 2 * x * y} = { (0, 0), (1, 0), (1/2, 1/2), (1/2, -1/2) } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x,y) satisfies both equations.
      rintro ⟨h1, h2⟩
      by_cases h3 : y = 0
      · -- If y = 0, then from h1: x = x², so x = 0 or 1
        rw [h3] at h1 h2
        have : x = 0 ∨ x = 1 := by
          have : x * (x - 1) = 0 := by linarith
          cases (mul_eq_zero.mp this) with
          | inl h4 => 
            left; linarith
          | inr h5 => 
            right; linarith
        cases this with
        | inl h4 => 
          simp [h4, h3]
        | inr h5 =>
          simp [h5, h3]
      · -- y ≠ 0
        -- From h2: y = 2xy
        -- y = 2xy => 1 = 2x (divided by y)
        have h4 : x = 1/2 := by
          apply (mul_left_inj' h3).mp
          linarith
        -- Substitute x = 1/2 into h1
        have h5 : y ^ 2 = 1/4 := by
          rw [h4] at h1
          nlinarith
        -- Solve y² = 1/4 to get y = ±1/2
        have h6 : y = 1/2 ∨ y = -1/2 := by
          have h7 : y ^ 2 - 1/4 = 0 := by linarith
          have h8 : (y - 1/2) * (y + 1/2) = 0 := by
            ring_nf at h7 ⊢
            linarith
          cases (mul_eq_zero.mp h8) with
          | inl h9 =>
            left
            linarith
          | inr h10 =>
            right
            linarith
        cases h6 with
        | inl h7 =>
          simp [h4, h7]
        | inr h8 =>
          simp [h4, h8]
    · -- Show that these points satisfy both equations
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (0, 0)
        constructor
        · norm_num
        · norm_num
      · -- (1, 0)
        constructor
        · norm_num
        · norm_num
      · -- (1/2, 1/2)
        constructor
        · norm_num
        · norm_num
      · -- (1/2, -1/2)
        constructor
        · norm_num
        · norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton, Prod.ext_iff]
  <;> norm_num