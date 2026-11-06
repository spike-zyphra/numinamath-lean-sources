import Mathlib

theorem number_theory_15449 {IsClever : ℕ → Prop} (isClever_def : ∀ n, IsClever n ↔
    Even n ∧ n > 20 ∧ n < 120 ∧ (Nat.digits 10 n).sum = 9) :
    {n | 27 ∣ n ∧ IsClever n}.ncard / {n | IsClever n}.ncard = (2 / 5 : ℚ) := by 
  have h1 : {n | IsClever n} = {36, 54, 72, 90, 108} := by
    ext n
    simp [isClever_def, Nat.even_iff]
    constructor
    · -- Assume n is clever
      intro h
      rcases h with ⟨h_even, h1, h2, h3⟩
      have h40 : n < 120 := by linarith
      have h21 : n > 20 := by linarith
      interval_cases n <;> norm_num at h_even h1 h2 h3 ⊢
      <;> tauto
    · -- Assume n ∈ {36, 54, 72, 90, 108}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- Show 36 is clever
        norm_num [Nat.even_iff, isClever_def]
      · -- Show 54 is clever
        norm_num [Nat.even_iff, isClever_def]
      · -- Show 72 is clever
        norm_num [Nat.even_iff, isClever_def]
      · -- Show 90 is clever
        norm_num [Nat.even_iff, isClever_def]
      · -- Show 108 is clever
        norm_num [Nat.even_iff, isClever_def]
  have h2 : {n | 27 ∣ n ∧ IsClever n} = {54, 108} := by
    ext n
    simp [h1, isClever_def, Nat.even_iff, Set.mem_setOf_eq]
    constructor
    · -- Assume n is clever and divisible by 27
      intro h
      rcases h with ⟨h27, ⟨h_even, h1, h2, h3⟩⟩
      have h40 : n < 120 := by linarith
      have h21 : n > 20 := by linarith
      interval_cases n <;> norm_num at h27 h_even h1 h2 h3 ⊢
      <;> tauto
    · -- Assume n ∈ {54, 108}
      rintro (rfl | rfl)
      · -- Show 54 is clever and divisible by 27
        constructor
        · -- Show 54 is divisible by 27
          norm_num 
        · -- Show 54 is clever
          norm_num [Nat.even_iff, isClever_def]
      · -- Show 108 is clever and divisible by 27
        constructor
        · -- Show 108 is divisible by 27
          norm_num 
        · -- Show 108 is clever
          norm_num [Nat.even_iff, isClever_def]
  rw [h1, h2]
  rw [Set.ncard_eq_toFinset_card']
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  all_goals norm_num
  <;> native_decide
  <;> native_decide
  <;> native_decide
  all_goals try native_decide