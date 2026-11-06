import Mathlib
theorem number_theory_611453 : {x : ℕ | x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4}.ncard = 84:= by
  have h1 : {x : ℕ | x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4} = Set.Icc 250 333 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First direction: if x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4 then 250 ≤ x ≤ 333
      intro h
      rcases h with ⟨hx_pos, hx1, hx2⟩
      have h2 : x ≥ 250 := by
        by_contra h
        push_neg at h
        interval_cases x <;> norm_num at hx2 <;> all_goals contradiction
      have h3 : x ≤ 333 := by
        by_contra h
        push_neg at h
        have h4 : x > 333 := by linarith
        have h5 : (Nat.digits 10 (3 * x)).length > 3 := by
          have h6 : x ≥ 334 := by linarith
          have h7 : 3 * x ≥ 1002 := by omega
          have h8 : (Nat.digits 10 (3 * x)).length ≥ 4 := by
            have : (Nat.log 10 (3 * x)) + 1 ≥ 4 := by
              have : Nat.log 10 (3 * x) ≥ 3 := by
                have h9 : 10 ^ 3 ≤ 3 * x := by omega
                exact Nat.le_log_of_pow_le (by norm_num) h9
              omega
            have h10 : (Nat.digits 10 (3 * x)).length = (Nat.log 10 (3 * x)) + 1 := by
              rw [Nat.digits_len]
              all_goals omega
            omega
          omega
        linarith
      constructor
      · exact h2
      · exact h3
    · -- Now the reverse direction: if 250 ≤ x ≤ 333 then x > 0 ∧ (Nat.digits 10 (3 * x)).length = 3 ∧ (Nat.digits 10 (4 * x)).length = 4
      rintro ⟨hx1, hx2⟩
      constructor
      · linarith
      constructor
      · -- (Nat.digits 10 (3 * x)).length = 3
        interval_cases x <;> norm_num <;> try trivial
        <;> omega
      · -- (Nat.digits 10 (4 * x)).length = 4
        interval_cases x <;> norm_num <;> try trivial
        <;> omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.Icc]
  <;> rfl