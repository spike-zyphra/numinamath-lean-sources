import Mathlib

theorem number_theory_287259 :
    {n | n ∈ Finset.range 120 ∧ (n % 3 = 0 ∧ n % 4 = 0 ∧ n % 10 = 0)}.ncard = 2 ∧
    {n | n ∈ Finset.range 120 ∧ (n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0)}.ncard = 56 := by
  have h1 : {n | n ∈ Finset.range 120 ∧ (n % 3 = 0 ∧ n % 4 = 0 ∧ n % 10 = 0)} = {0, 60} := by
    ext n
    simp [Finset.mem_range]
    constructor
    · -- Show that if n is in the set, then n in {0, 60}
      rintro ⟨h, ⟨h3, h4, h10⟩⟩
      omega
    · -- Show that if n in {0, 60}, then it is in the set
      rintro (rfl | rfl)
      · -- n = 0
        constructor
        · norm_num
        · norm_num
      · -- n = 60
        constructor
        · norm_num
        · norm_num
  have h2 : {n | n ∈ Finset.range 120 ∧ (n % 3 = 0 ∧ n % 4 = 0 ∧ n % 10 = 0)}.ncard = 2 := by
    rw [h1]
    rw [Set.ncard_pair]
    all_goals norm_num
  have h3 : {n | n ∈ Finset.range 120 ∧ (n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0)}.ncard = 56 := by
    have h4 : {n | n ∈ Finset.range 120 ∧ (n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0)} = Finset.filter (fun n => n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0) (Finset.range 120) := by
      ext n
      simp
    rw [h4]
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor
  · exact h2
  · exact h3