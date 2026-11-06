import Mathlib

theorem algebra_138445 :
    {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℚ) + (2 / n : ℚ) = 1}.encard = 4 := by
  have h1 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℚ) + (2 / n : ℚ) = 1} = {(5, 10), (6, 6), (8, 4), (12, 3)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- First, prove that if $(m, n)$ is in the set, then it's one of the four pairs.
      rintro ⟨hm, hn, heq⟩
      have h_eq : (m : ℚ) > (0 : ℚ) := by exact_mod_cast hm
      have h_eq2 : (n : ℚ) > (0 : ℚ) := by exact_mod_cast hn
      have h_eq3 : (m * (n : ℚ) ) = (4 * (n : ℚ) + 2 * (m : ℚ) ) := by
        have hne1 : (m : ℚ) ≠ 0 := by positivity
        have hne2 : (n : ℚ) ≠ 0 := by positivity
        field_simp at heq ⊢
        nlinarith [heq]
      have h2 : m * n = 4 * n + 2 * m := by
        exact_mod_cast h_eq3
      have h3 : m ≤ 12 := by
        by_contra h
        push_neg at h
        have h4 : n ≤ 3 := by
          nlinarith [show m * n = 4 * n + 2 * m from h2, h]
        interval_cases n <;> try { 
          omega
        }
        all_goals nlinarith
      have h4 : n ≤ 12 := by
        by_contra h
        push_neg at h
        have h5 : m ≤ 4 := by
          nlinarith [show m * n = 4 * n + 2 * m from h2, h]
        interval_cases m <;> try { 
          omega 
        }
        all_goals nlinarith
      interval_cases m <;> try { 
        omega 
      }
      all_goals try { 
        interval_cases n <;> norm_num at h2 <;> norm_num [Prod.ext_iff] at *
        <;> tauto 
      }
    · -- Now, prove the converse: if $(m, n)$ is in the finite set, then it's in the original set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- First pair (5, 10)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Second pair (6, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Third pair (8, 4)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Fourth pair (12, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { 
    all_goals try { 
      tauto 
    } 
  }
  all_goals norm_num
  <;> try { 
    tauto 
  } <;> try { 
    aesop 
  }