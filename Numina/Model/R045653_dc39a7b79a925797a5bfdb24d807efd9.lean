import Mathlib

theorem algebra_6317 :
  ∑ᶠ x ∈ {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / 5}, x.1 = 46 := by
  have h1 : {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / 5} = {(6, 30), (10, 10), (30, 6)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h, prove {(6, 30), (10, 10), (30, 6)}
      rintro ⟨hx, hy, heq⟩
      have h_eq : (x : ℚ) * (y : ℚ) = 5 * (x : ℚ) + 5 * (y : ℚ) := by
        field_simp at heq ⊢
        linarith
      have h_eq2 : (x : ℤ) * (y : ℤ) = 5 * (x : ℤ) + 5 * (y : ℤ) := by
        exact_mod_cast h_eq
      have h2 : x ≤ 30 := by
        by_contra h
        push_neg at h
        have h3 : y ≤ 30 := by
          nlinarith [sq_nonneg (x - 30: ℤ), sq_nonneg (y - 6: ℤ), mul_pos hx hy]
        interval_cases y <;> try { 
          omega 
        }
      have h3 : y ≤ 30 := by
        by_contra h
        push_neg at h
        have h3 : x ≤ 30 := by
          nlinarith [sq_nonneg (y - 30: ℤ), sq_nonneg (x - 6: ℤ), mul_pos hx hy]
        interval_cases x <;> try { 
          omega 
        }
      interval_cases x <;> try { 
        omega 
      }
      <;> try { 
        omega 
      }
      <;> try { 
        tauto 
      }
    · -- Show that these are indeed solutions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try native_decide
  all_goals norm_num
  all_goals native_decide
  all_goals try native_decide