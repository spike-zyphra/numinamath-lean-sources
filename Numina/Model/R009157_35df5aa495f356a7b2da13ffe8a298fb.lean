import Mathlib
theorem number_theory_15941 :6 ∈ {n | n * 10 % 8 = 4} ∧ {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6}.ncard = 1 := by
  constructor
  · -- Show 6 ∈ {n | n * 10 % 8 = 4}
    norm_num
  · -- Show {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6}.ncard = 1
    have h1 : {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6} = {2} := by
      ext n
      simp -- Unfold the definition of the set
      constructor
      · -- Assume n ∈ {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6}
        intro h
        rcases h with ⟨h1, h2⟩
        interval_cases n <;> tauto
      · -- Show n ∈ {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6} from n = 2
        intro h
        rcases h with rfl
        constructor
        · -- Show 2 * 10 % 8 = 4
          norm_num
        · -- Show 2 < 6
          all_goals norm_num
    rw [h1]
    simp -- Show {2} has cardinality 1
    <;> try { native_decide }
    <;> try { native_decide }
    all_goals norm_num