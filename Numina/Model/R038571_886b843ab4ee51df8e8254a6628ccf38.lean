import Mathlib

theorem algebra_19684 :
    Set.ncard {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ∈ Finset.Icc 1 6 ∧ b ∈ Finset.Icc 1 6 ∧ a ≠ b ∧ ¬(a * b = 6)} = 13 := by
  have h1 : {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ∈ Finset.Icc 1 6 ∧ b ∈ Finset.Icc 1 6 ∧ a ≠ b ∧ ¬(a * b = 6)} = 
      { {1, 2}, {1, 3}, {1, 4}, {1, 5}, 
        {2, 4}, {2, 5}, {2, 6},
        {3, 4}, {3, 5}, {3, 6}, 
        {4, 5}, {4, 6},
        {5, 6}
      } := by
    ext s 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor 
    · -- Assume s is in left side, prove it's in the right side
      rintro ⟨a, b, h1, ha1, hb1, hneq, hpro⟩
      have h2 : a ≥ 1 := by 
        simp [Finset.mem_Icc] at ha1 
        exact ha1.1
      have h3 : a ≤ 6 := by 
        simp [Finset.mem_Icc] at ha1 
        exact ha1.2
      have h4 : b ≥ 1 := by 
        simp [Finset.mem_Icc] at hb1 
        exact hb1.1
      have h5 : b ≤ 6 := by 
        simp [Finset.mem_Icc] at hb1 
        exact hb1.2
      rw [show s = {a, b} by exact_mod_cast h1] 
      interval_cases a <;> interval_cases b 
        <;> norm_num [hneq, hpro] at *
        <;> aesop 
    · -- Assume s is in right side, prove it's in left side
      rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
      · -- Case {1, 2}
        rw [h]
        refine' ⟨1, 2, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {1, 3}
        rw [h]
        refine' ⟨1, 3, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {1, 4}
        rw [h]
        refine' ⟨1, 4, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {1, 5}
        rw [h]
        refine' ⟨1, 5, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {2, 4}
        rw [h]
        refine' ⟨2, 4, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {2, 5}
        rw [h]
        refine' ⟨2, 5, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {2, 6}
        rw [h]
        refine' ⟨2, 6, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {3, 4}
        rw [h]
        refine' ⟨3, 4, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {3, 5}
        rw [h]
        refine' ⟨3, 5, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {3, 6}
        rw [h]
        refine' ⟨3, 6, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {4, 5}
        rw [h]
        refine' ⟨4, 5, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {4, 6}
        rw [h]
        refine' ⟨4, 6, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Case {5, 6}
        rw [h]
        refine' ⟨5, 6, rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide