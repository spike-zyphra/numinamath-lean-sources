import Mathlib

theorem number_theory_189797 :
    Set.ncard {x : ℕ | ∃ m n, x = (m * n + 1) / (m + n) ∧ m > 0 ∧ n > 0 ∧ x ≤ 2004} = 2004 := by
  have h1 : {x : ℕ | ∃ m n, x = (m * n + 1) / (m + n) ∧ m > 0 ∧ n > 0 ∧ x ≤ 2004} = Set.Icc 1 2004 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨m, n, h_eq, hm_pos, hn_pos, hx_le⟩
      have h2 : x ≥ 1 := by
        rw [h_eq]
        have h6 : (m * n + 1) >= (m + n) := by
          nlinarith [mul_nonneg (show m >= 0 by linarith) (show n >= 0 by linarith), sq_nonneg (m - 1), sq_nonneg (n - 1)]
        have h7 : (m + n) > 0 := by
          linarith
        have h8 : ((m * n + 1) ) / (m + n) >= 1 := by
          have h9 : (m * n + 1) >= (m + n) := by
            nlinarith [mul_nonneg (show m >= 0 by linarith) (show n >= 0 by linarith), sq_nonneg (m - 1), sq_nonneg (n - 1)]
          have h10 : (m + n) > 0 := by 
            linarith
          have h11 : ((m * n + 1) ) / (m + n) >= ( (m + n) ) / (m + n) := by
            apply Nat.div_le_div
            all_goals linarith
          have h12 : ( (m + n) ) / (m + n) = 1 := by
            field_simp
          linarith [h11, h12, h9]
          all_goals linarith
        linarith
      constructor
      · linarith
      · linarith
    · rintro ⟨hx1, hx2⟩
      have hk : ∃ m n, x = (m * n + 1) / (m + n) ∧ m > 0 ∧ n > 0 ∧ x ≤ 2004 := by
        use 2 * x - 1, 2 * x + 1
        constructor
        · -- Show equality of the division
          have eqn : ( (2 * x - 1) * (2 * x + 1) + 1 ) / ( (2 * x - 1) + (2 * x + 1) ) = x := by
            have h1 : (2 * x - 1) * (2 * x + 1) + 1 = 4 * x * x := by
              cases x with
              | zero =>
                exfalso
                linarith
              | succ n =>
                cases n with
                | zero =>
                  simp
                | succ n =>
                  simp [Nat.add_assoc, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
                  ring_nf
                  <;> omega
            have h4 : ( (2 * x - 1) + (2 * x + 1) ) = 4 * x := by
              cases x with
              | zero =>
                exfalso
                linarith
              | succ n =>
                cases n with
                | zero =>
                  simp
                | succ n =>
                  simp [Nat.add_assoc, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
                  ring_nf
                  <;> omega
            have h5 : 4 * x > 0 := by
              nlinarith
            have eqn1 : (4 * x * x ) / (4 * x) = x := by
              have h5' : 4 * x > 0 := h5
              field_simp
              <;> nlinarith
            calc
              ( (2 * x - 1) * (2 * x + 1) + 1 ) / ( (2 * x - 1) + (2 * x + 1) )
                  = (4 * x * x ) / (4 * x) := by rw [h1, h4]
              _ = x := by rw [eqn1]
          linarith [eqn]
        constructor
        · -- Show m > 0
          have h6 : 2 * x - 1 > 0 := by
            omega
          linarith
        constructor
        · -- Show n > 0
          have h7 : 2 * x + 1 > 0 := by
            omega
          linarith
        · linarith
      exact hk
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.Icc]
  <;> try native_decide