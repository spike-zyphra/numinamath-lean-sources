import Mathlib

theorem algebra_21978 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / ((1 / x + 1 / y) / 2 : ℝ) = 20}.encard = 9 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / ((1 / x + 1 / y) / 2 : ℝ) = 20} = 
    {(11, 110), (110, 11), (12, 60), (60, 12), (14, 35), (35, 14), (15, 30), (30, 15), (20, 20)} := by
    ext ⟨x, y⟩
    simp 
    constructor
    · -- Assume that (x, y) is in the set 
      rintro ⟨hx, hy, heq⟩
      have h2 : (x : ℝ) > 0 := by exact_mod_cast hx
      have h3 : (y : ℝ) > 0 := by exact_mod_cast hy
      field_simp at heq
      have h4 : (x : ℝ) * (y : ℝ) = 10 * ((x : ℝ) + (y : ℝ)) := by
        nlinarith 
      have h5 : (x : ℕ) * (y : ℕ) = 10 * (x + y) := by
        exact_mod_cast h4
      have h6 : x ≤ 110 := by
        by_contra h
        push_neg at h
        have h7 : y ≤ 10 := by
          nlinarith [h5, h]
        interval_cases y <;> omega
      have h7 : y ≤ 110 := by
        by_contra h
        push_neg at h
        have h8 : x ≤ 10 := by
          nlinarith [h5, h]
        interval_cases x <;> omega
      interval_cases x <;> omega
    · -- Show that these 9 pairs satisfy the condition
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Show (11, 110) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (110, 11) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (12, 60) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (60, 12) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (14, 35) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (35, 14) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (15, 30) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (30, 15) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
      · -- Show (20, 20) 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> aesop