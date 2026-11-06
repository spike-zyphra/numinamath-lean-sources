import Mathlib

/- How many pairs of positive integers $(a, b)$ with $\leq b$ satisfy $\frac{1}{a}+\frac{1}{b}=\frac{1}{6}$ ? -/
theorem algebra_608384 :
    Set.encard {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ a ≤ b ∧ 1 / a + 1 / b = (1 / 6 : ℚ)} = 5 := by
  -- It suffices to show that the set is equal to {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12)}, which has 5 elements
  suffices H : {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ a ≤ b ∧ 1 / a + 1 / b = (1 / 6 : ℚ)} = {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12)} by
    rw [H]
    convert Set.encard_coe_eq_coe_finsetCard ({(7, 42), (8, 24), (9, 18), (10, 15), (12, 12)} : Finset (ℤ × ℤ))
    simp
  ext ⟨a, b⟩
  simp
  constructor
  -- We first verify that the pairs satisfy the equation
  swap
  {
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals norm_num
  }
  -- Let a, b be positive integers with a ≤ b and 1/a + 1/b = 1/6
  intro ⟨ha, hb, hab, h⟩
  -- Cancel the denominators at the equation
  field_simp at h
  -- Cast it back to ℤ
  norm_cast at h
  -- We have (a - 6)(b - 6) = 36
  replace h : (a - 6) * (b - 6) = 36 := by linear_combination -h
  -- We have 6 ≤ a ≤ 12, which can be solved using nlinarith
  replace ha : 6 ≤ a := by nlinarith
  replace hab : a ≤ 12 := by nlinarith
  -- Now a = 6, 7, 8, 9, 10, 11, 12, we check each case
  interval_cases a
  all_goals omega
