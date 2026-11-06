import Mathlib

theorem algebra_264565 : {(x, y) : ℤ × ℤ | 2*x^2 + x*y + y^2 - x + 2*y + 1 = 0}.ncard = 3 := by
  have h1 : {(x, y) : ℤ × ℤ | 2*x^2 + x*y + y^2 - x + 2*y + 1 = 0} = { (1, -2), (0, -1), (1, -1) } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) is a solution
      rintro H
      have h2 : y ≥ -2 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y + 1), sq_nonneg (x - y - 1), sq_nonneg (2 * x + y - 1)]
      have h3 : y ≤ 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y + 1), sq_nonneg (x - y - 1), sq_nonneg (2 * x + y - 1)]
      interval_cases y <;> try { 
        have : x ≤ 2 := by nlinarith 
        have : x ≥ -1 := by nlinarith
        interval_cases x <;> tauto 
      }
    · -- Show that (x, y) ∈ { (1, -2), (0, -1), (1, -1) } is a solution
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
      all_goals
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }