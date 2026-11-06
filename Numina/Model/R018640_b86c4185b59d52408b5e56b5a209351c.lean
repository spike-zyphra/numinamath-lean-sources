import Mathlib

def is_seven_star (N : ℕ) : Prop :=
  {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard ≥ 7

theorem number_theory_178965 :
    IsLeast {N | 2000 < N ∧ is_seven_star N} 2016 := by
  constructor
  · -- Show that 2016 is in the set
    constructor
    · norm_num
    · -- Show that 2016 is a seven star number
      have h1 : is_seven_star 2016 := by
        unfold is_seven_star
        have : {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0} = {1, 2, 3, 4, 6, 7, 8, 9} := by
          ext k
          simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
            Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
          constructor
          · -- First implication: if k in the set {k | k in [1,9] ∧ 2016 % k = 0}, then k in {1,2,3,4,6,7,8,9}
            rintro ⟨⟨hk1, hk2⟩, hdiv⟩
            interval_cases k <;> norm_num at *
          · -- Second implication: if k in {1,2,3,4,6,7,8,9}, then k in {k | k in [1,9], 2016 % k = 0}
            rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · constructor
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
            · constructor 
              · norm_num
              · norm_num
        rw [this]
        rw [Set.ncard_eq_toFinset_card']
        simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
        <;> try native_decide
      tauto
  · -- Show that 2016 is minimal
    intro N h
    rcases h with ⟨h1, h2⟩
    by_contra h3
    push_neg at h3
    have h4 : N < 2016 := h3
    have h5 : is_seven_star N := h2
    unfold is_seven_star at h5
    have h6 : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard < 7 := by
      have hN1 : N > 2000 := h1
      have hN2 : N < 2016 := h4
      have h7 : N ≤ 2015 := by 
        omega
      have h3 : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0} = Finset.filter (fun (k : ℕ) => N % k = 0) (Finset.Icc 1 9) := by 
        ext k
        simp 
      rw [h3]
      rw [Set.ncard_coe_Finset]
      interval_cases N <;> native_decide 
    omega