import Mathlib

theorem number_theory_16104 :
    Set.ncard {b | b ∈ Finset.Icc 2 9 ∧ (Nat.digits b 576).headI = 1} = 1 := by
  have : {b | b ∈ Finset.Icc 2 9 ∧ (Nat.digits b 576).headI = 1} = {5} := by
    ext b
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First, prove the forward direction: if b ∈ {b | b ∈ [2, 9] ∧ ...}, then b = 5
      rintro ⟨⟨h2, h9⟩, h1⟩
      interval_cases b <;> norm_num at h1 ⊢ <;> tauto
    · -- Now, prove the reverse: if b = 5, then it's in the set
      intro hb
      rw [hb]
      constructor
      · -- 5 is in range [2, 9]
        norm_num
      · -- check the last digit
        native_decide
  rw [this]
  simp