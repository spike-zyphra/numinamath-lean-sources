import Mathlib

theorem algebra_252361 {n : ℕ} (npos : 0 < n) :
    (∃ P V, 0 < P ∧ 0 < V ∧ n * (P - 2) = V + 2 ∧ 2 * (V - n) = P + n)
    ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8 := by
  constructor
  · -- Assume the existence of P, V satisfying the conditions, prove n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8
    intro h
    rcases h with ⟨P, V, hP, hV, h1, h2⟩
    by_cases hn : n ≤ 9
    · -- If $n \le 9$, then $n=1,2,3,4,5,6,7,8,9$
      interval_cases n <;> omega -- it will work for n = 1, 2, 3, 8
    · -- Assume n > 9
      push_neg at hn
      have h3 : P > 2 := by
        by_contra h
        push_neg at h
        have : P ≤ 2 := by omega
        interval_cases P <;> omega
      have eq1 : n * (P - 2) = V + 2 := h1
      have eq2 : 2 * (V - n) = P + n := h2
      -- Derive a bound for P
      have eq3 : P * (2 * n - 1) = 7 * n + 4  := by
        cases P with
        | zero => omega -- contradiction
        | succ p =>
          cases p with
          | zero => omega -- contradiction
          | succ p =>
            cases p with
            | zero => 
              omega -- contradiction
            | succ p =>
              simp [Nat.mul_sub, Nat.sub_mul, Nat.mul_comm] at eq1 eq2 ⊢
              all_goals 
                ring_nf at eq1 eq2 ⊢
                omega
      -- Derive the bound that n ≤ 9, which contradicts our assumption
      have h41 : n ≤ 9  := by
        have eq4 : P * (2 * n - 1) = 7 * n + 4 := eq3
        have h4 : P ≤ 7 := by
          by_contra h5
          push_neg at h5
          have h5 : P ≥ 8  := by omega
          have eq7  : (2 * n - 1) * 8 ≤ 7 * n + 4 := by
            have eq44  : (2 * n - 1) * P = 7 * n + 4 := by 
              nlinarith 
            have eq8  : (2 * n - 1) * 8 ≤ (2 * n - 1) * P := by 
              apply Nat.mul_le_mul_left 
              all_goals 
                omega 
            nlinarith
          omega
        interval_cases P <;> omega -- Intersection possible finite cases within small p ≤7.
      omega
  · -- Assume n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8, prove exist $P V
    rintro (h | h | h | h)
    · -- When n = 1
      rw [h]
      use 11, 7
      all_goals norm_num
    · -- When n = 2
      rw [h]
      use 6, 6
      all_goals norm_num
    · -- When n = 3
      rw [h]
      use 5, 7
      all_goals norm_num
    · -- When n = 8
      rw [h]
      use 4, 14
      all_goals norm_num