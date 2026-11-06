import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem algebra_852 :
  Set.ncard {k : ℤ | ∃ x y : ℤ, y = x - 3 ∧ y = k * x + k} = 6 := by 
  have : {k : ℤ | ∃ x y : ℤ, y = x - 3 ∧ y = k * x + k} = {-3, -1, 0, 2, 3, 5} := by 
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume k is in the left side
      rintro ⟨x, y, h1, h2⟩
      have h3 : k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = -1 ∨ k = -3 := by
        have eq1 : x * (1 - k) = 3 + k := by
          linarith
        have h4 : (1 - k) ∣ (3 + k) := by
          use x
          all_goals
            linarith 
        have h9 : k - 1 ∣ 4 := by
          have h14 : k - 1 ∣ 3 + k := by
            have h15 : (1 - k) ∣ (3 + k) := h4
            have h16 : k - 1 ∣ (3 + k) := by
              have : (k - 1) = - (1 - k) := by ring
              rw [this] 
              exact Int.neg_dvd.2 h15 
            exact h16 
          have h15 : k - 1 ∣ (3 + k - (k - 1)) := by
            apply Dvd.dvd.sub 
            · exact h14 
            · exact Int.dvd_refl (k - 1) 
          have h16 : 3 + k - (k - 1) = 4 := by 
            omega 
          rw [h16] at h15 
          exact h15 
        have h17 : k - 1 ≤ 4 := by 
          apply Int.le_of_dvd (by norm_num) h9 
        have h18 : k - 1 ≥ -4 := by 
          have h20 : - (k - 1) ∣ 4 := by 
            exact Int.neg_dvd.2 h9 
          have h21 : - (k - 1) ≤ 4 := by 
            apply Int.le_of_dvd (by norm_num) h20 
          linarith 
        have h22 : k ≤ 5 := by 
          omega 
        have h23 : k ≥ -3 := by 
          omega 
        interval_cases k <;> tauto 
      tauto 
    · -- Show the existence of integer points (x,y) at the intersection for each k ∈ {-3, -1, 0, 2, 3, 5}.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · refine ⟨0, -3, by norm_num, by norm_num⟩ 
      · refine ⟨1, -2, by norm_num, by norm_num⟩ 
      · refine ⟨3, 0, by norm_num, by norm_num⟩ 
      · refine ⟨-5, -8, by norm_num, by norm_num⟩ 
      · refine ⟨-3, -6, by norm_num, by norm_num⟩ 
      · refine ⟨-2, -5, by norm_num, by norm_num⟩ 
  rw [this] 
  rw [Set.ncard_eq_toFinset_card']
  simp