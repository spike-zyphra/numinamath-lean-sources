import Mathlib

theorem algebra_233138 : {(x, y) : ℤ × ℤ | x ^ 2 + x * y + 2 * y ^ 2 = 29}.ncard = 4 := by 
  have h1 : {(x, y) : ℤ × ℤ | x ^ 2 + x * y + 2 * y ^ 2 = 29} = { (3, -4), (1, -4), (-1, 4), (-3, 4) } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h: x ^ 2 + x * y + 2 * y ^ 2 = 29, derive equality
      intro h
      have h2 : x ^ 2 + x * y + 2 * y ^ 2 = 29 := h
      have h3 : y ≤ 4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - 4), sq_nonneg (2 * x + y), sq_nonneg (x - 4), sq_nonneg (x - y), sq_nonneg (x + 4)]
      have h4 : y ≥ -4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (y + 4), sq_nonneg (2 * x + y), sq_nonneg (x + 4), sq_nonneg (x - y), sq_nonneg (x - (-4))]
      interval_cases y <;> try { 
        have : x ≤ 7 := by nlinarith
        have : x ≥ -8 := by nlinarith
        interval_cases x <;> tauto
        <;> tauto
      }
      all_goals try { 
        omega
        <;> try { norm_num at h2 <;> tauto }
      }
    · -- Assume h: pair is one of the solutions, derive equality
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
      · -- Check solution (3, -4)
        norm_num
      · -- Check solution (1, -4)
        norm_num
      · -- Check solution (-1, 4)
        norm_num
      · -- Check solution (-3, 4)
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }
  <;> try { trivial }