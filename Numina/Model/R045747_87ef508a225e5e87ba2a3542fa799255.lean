import Mathlib

theorem algebra_3552 : {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 = x * y + 2 * x + 2 * y}.encard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 = x * y + 2 * x + 2 * y} = {(0, 0), (2, 0), (0, 2), (4, 2), (2, 4), (4, 4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h
      rintro h
      have h2 : x ≤ 6 := by
        nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x - y)]
      have h3 : x ≥ -2 := by
        nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (x - y)]
      have h4 : y ≤ 6 := by
        nlinarith [sq_nonneg (y - 6), sq_nonneg (x - 6), sq_nonneg (y - x)]
      have h5 : y ≥ -2 := by
        nlinarith [sq_nonneg (y + 2), sq_nonneg (x + 2), sq_nonneg (y - x)]
      interval_cases x <;> interval_cases y
      <;> norm_num at h ⊢
      <;> tauto
    · -- Show that if h holds, then (x,y) in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (0, 0)
        norm_num
      · -- Check (2, 0)
        norm_num
      · -- Check (0, 2)
        norm_num
      · -- Check (4, 2)
        norm_num
      · -- Check (2, 4)
        norm_num
      · -- Check (4, 4)
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }