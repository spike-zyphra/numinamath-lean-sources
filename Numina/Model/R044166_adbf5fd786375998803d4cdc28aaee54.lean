import Mathlib

theorem number_theory_131668 :
    {(x, y) : ℤ × ℤ | 12 * x ^ 2 + 7 * y ^ 2 = 4620}.ncard = 8 ∧
    {(x, y) : ℤ × ℤ | 12 * x ^ 2 + 7 * y ^ 2 = 4620} =
    {(7, 24), (14, 18), (-7, -24), (-14, -18), (7, -24), (14, -18), (-7, 24), (-14, 18)} := by 
  have h1 : {(x, y) : ℤ × ℤ | 12 * x ^ 2 + 7 * y ^ 2 = 4620} =
      {(7, 24), (14, 18), (-7, -24), (-14, -18), (7, -24), (14, -18), (-7, 24), (-14, 18)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume 12 * x^2 + 7 * y^2 = 4620, show (x, y) is in the set
      rintro H
      have h2 : x ^ 2 ≤ 385 := by
        nlinarith [show 12 * x ^ 2 + 7 * y ^ 2 = 4620 from H, sq_nonneg (y), sq_nonneg (x)]
      have h3 : y ^ 2 ≤ 660 := by
        nlinarith [show 12 * x ^ 2 + 7 * y ^ 2 = 4620 from H, sq_nonneg (y), sq_nonneg (x)]
      have h4 : x ≤ 19 := by
        nlinarith [show x ^ 2 ≤ 385 by nlinarith, sq_nonneg (x + 19)]
      have h5 : x ≥ -19 := by
        nlinarith [show x ^ 2 ≤ 385 by nlinarith, sq_nonneg (x - 19)]
      have h6 : y ≤ 25 := by
        nlinarith [show y ^ 2 ≤ 660 by nlinarith, sq_nonneg (y + 25)]
      have h7 : y ≥ -25 := by
        nlinarith [show y ^ 2 ≤ 660 by nlinarith, sq_nonneg (y - 25)]
      interval_cases x <;> interval_cases y <;> norm_num at H ⊢
    · -- Show that (x, y) in the set satisfies the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals norm_num
  constructor
  · -- Show that the cardinality is 8
    rw [h1]
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset]
    <;> try { native_decide }
  · -- Show that the sets are equal
    exact h1