import Mathlib

theorem algebra_13025 :
    ∑ᶠ x ∈ {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ (7 / x : ℚ) - (8 / y : ℚ) = 1}, x = 14 := by 
  have h1 : {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ (7 / x : ℚ) - (8 / y : ℚ) = 1} = {3, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward: if x in the set, then x in {3,5,6}
      rintro ⟨y, hx, hy, heq⟩
      have h2 : (x : ℚ) > 0 := by exact_mod_cast hx
      have h3 : (y : ℚ) > 0 := by exact_mod_cast hy
      have h4 : 7 * (y : ℚ) - 8 * (x : ℚ) = (x : ℚ) * (y : ℚ) := by
        have h1 : (x : ℚ) ≠ 0 := by exact_mod_cast show x ≠ 0 by omega
        have h2 : (y : ℚ) ≠ 0 := by exact_mod_cast show y ≠ 0 by omega
        have eq3 : (7 / (x : ℚ) - 8 / (y : ℚ) = (1 : ℚ)) := by
          simpa using heq
        field_simp [h1, h2] at eq3 ⊢
        nlinarith
      have h5 : (7 * (y : ℚ) = (8 * (x : ℚ) + (x : ℚ) * (y : ℚ))) := by
        linarith
      have h6 : 7 * y = 8 * x + x * y := by
        exact_mod_cast h5
      have h7 : x ≤ 7 := by 
        by_contra h8
        push_neg at h8
        have h8' : x ≥ 8 := by omega
        nlinarith [sq_nonneg ((y : ℤ) ), sq_nonneg ((x : ℤ) ), sq_nonneg ((y : ℤ) - 48), sq_nonneg ((x : ℤ) - 6 : ℤ), sq_nonneg ((y : ℤ) - 20 : ℤ), sq_nonneg ((x : ℤ) - 5 : ℤ), sq_nonneg ((y : ℤ) - 6 : ℤ), sq_nonneg ((x : ℤ) - 3 : ℤ)
        ]
      interval_cases x <;> try { 
        omega
      } <;> try { 
        have h9 : y ≤ 56 := by 
          nlinarith
        interval_cases y <;> norm_num at h6 <;> 
          tauto 
      }
    · -- Backward: if x in {3,5,6}, then x in the set
      rintro (rfl | rfl | rfl)
      · -- x=3
        use 6
        all_goals norm_num
      · -- x=5
        use 20
        all_goals norm_num
      · -- x=6
        use 48
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try { 
    all_goals try { 
      native_decide 
    } 
  }
  <;> try { 
    try { 
      nlinarith 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        native_decide 
      }
    }
    <;> try { 
      omega 
    }
  }