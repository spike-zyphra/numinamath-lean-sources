import Mathlib

theorem number_theory_11784 :
    Set.ncard {x : ℕ | x < 100 ∧ 5 ∣ x ∧ x % 10 = 5} = 10 := by
  have h1 : {x : ℕ | x < 100 ∧ 5 ∣ x ∧ x % 10 = 5} = {5, 15, 25, 35, 45, 55, 65, 75, 85, 95} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in the left set, prove it in the right
      intro h
      rcases h with ⟨h1, h2, h3⟩
      have h1' : x < 100 := h1
      have h2' : 5 ∣ x := h2
      have h3' : x % 10 = 5 := h3
      interval_cases x <;> omega
    · -- Assume x in the right set, prove it in the left
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 5
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 15
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 25
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 35
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 45
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 55
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 65
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 75
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 85
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 95
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  norm_num