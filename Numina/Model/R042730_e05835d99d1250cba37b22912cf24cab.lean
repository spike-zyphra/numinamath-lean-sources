import Mathlib

theorem algebra_302908 :
    {(x, y) : ℤ × ℤ | |x * y| + |x + y| = 1}.ncard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | |x * y| + |x + y| = 1} = {(0, 1), (0, -1), (1, 0), (-1, 0), (1, -1), (-1, 1)} := by 
    ext ⟨x, y⟩ 
    simp
    constructor
    · -- Forward: if (x, y) in the set then in the explicit set 
      rintro H
      have h2 : |x * y| + |x + y| = 1 := H 
      have h_nonneg1 : 0 ≤ |x * y| := abs_nonneg _
      have h_nonneg2 : 0 ≤ |x + y| := abs_nonneg _
      have h3 : |x * y| ≤ 1 := by
        omega 
      have h4 : |x + y| ≤ 1 := by
        omega 
      have h5 : |x * y| = 0 ∨ |x * y| = 1 := by
        omega
      have h6 : |x + y| = 0 ∨ |x + y| = 1 := by
        omega
      cases h5 with
      | inl h50 => -- h50 is |x*y|=0
        have h61 : |x + y| = 1 := by
          omega 
        have h7 : x * y = 0 := by
          rw [abs_eq_zero] at h50 
          linarith
        have h8 : x = 0 ∨ y = 0 := by
          cases (mul_eq_zero.mp h7) with 
          | inl h9 =>
            left 
            linarith 
          | inr h10 =>
            right 
            linarith 
        rcases h8 with hx0 | hy0
        · -- x = 0 
          have h9 : y = 1 ∨ y = -1 := by 
            rw [hx0] at h61 
            cases eq_or_eq_neg_of_abs_eq h61 with
            | inl h10 =>
              omega
            | inr h11 =>
              omega
          rcases h9 with hy1 | hy1 
          · -- y = 1 
            simp [hx0, hy1]
          · -- y = -1 
            simp [hx0, hy1]
        · -- y = 0 
          have h9 : x = 1 ∨ x = -1 := by 
            rw [hy0] at h61 
            cases eq_or_eq_neg_of_abs_eq h61 with
            | inl h10 =>
              omega 
            | inr h11 =>
              omega 
          rcases h9 with hx1 | hx1
          · -- x = 1 
            simp [hx1, hy0]
          · -- x = -1 
            simp [hx1, hy0]
      | inr h51 => -- h51 is |x*y|=1
        have h60 : |x + y| = 0 := by
          omega 
        have h7 : x + y = 0 := by 
          rwa [abs_eq_zero] at h60 
        have h8 : y = -x := by 
          omega 
        have h10 : x ^ 2 = 1 := by
          rw [show y = -x by linarith [h8]] at h51
          have h11 : |x * (-x)| = |(x * (-x))| := by rfl
          have h12 : |(x * (-x))| = |(- (x ^ 2))| := by 
            ring_nf 
          have h13 : |(- (x ^ 2))| = |x ^ 2| := by
            rw [show - (x^2) = - (x ^ 2) by rfl]
            rw [abs_neg]
          have h14 : |x ^ 2| = x ^ 2 := by
            apply abs_of_nonneg 
            positivity
          linarith [h51, h12, h13, h14]
        have h11 : x = 1 ∨ x = -1 := by 
          have h12 : x ^ 2 - 1 = 0 := by
            linarith 
          have h13 : (x - 1) * (x + 1) = 0 := by
            linarith [h12]
          cases (mul_eq_zero.mp h13) with 
          | inl h14 =>
            left 
            linarith 
          | inr h15 =>
            right 
            linarith
        cases h11 with
        | inl hx1 => 
          have hy1 : y = -1 := by 
            linarith [h8, hx1]
          simp [hx1, hy1]
        | inr hx1 => 
          have hy1 : y = 1 := by 
            linarith [h8, hx1]
          simp [hx1, hy1]
    · -- Backward direction: all element in the explicit set in the set 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }