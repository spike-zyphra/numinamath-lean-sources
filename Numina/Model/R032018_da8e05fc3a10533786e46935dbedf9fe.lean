import Mathlib

theorem number_theory_133670 : {x : ℕ | 1 ≤ x ∧ x < 6000 ∧ 7 ∣ x ∧ ∃ n, x = n^2}.encard = 11 := by
  have h : {x : ℕ | 1 ≤ x ∧ x < 6000 ∧ 7 ∣ x ∧ ∃ n, x = n^2} = {49, 196, 441, 784, 1225, 1764, 2401, 3136, 3969, 4900, 5929} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the set
      intro h
      rcases h with ⟨h1, h2, h3, ⟨n, hn⟩⟩
      rw [hn] at h1 h2 h3
      have h4 : n ≤ 77 := by nlinarith
      interval_cases n <;> norm_num at hn h1 h2 h3 ⊢
      <;> omega
    · -- Assume x in the explicit set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨7, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨14, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨21, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨28, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨35, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨42, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨49, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨56, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨63, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨70, by norm_num⟩⟩
      · refine ⟨by norm_num, by norm_num, by norm_num, ⟨77, by norm_num⟩⟩
  rw [h]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }