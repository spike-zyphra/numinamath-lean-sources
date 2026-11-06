import Mathlib

set_option maxHeartbeats 500000
theorem combinatorics_608723 (S : Finset (Fin 8 → Fin 2))
  (hS : ∀ a : Fin 8 → Fin 2, a ∈ S ↔
  (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) = 5)
  : S.card = 9 := by

  -- Solution set is given by T, there are only 9 solutions
  let T : Finset (Fin 8 → Fin 2) := {
    λ x => if x = 2 then 0 else 1,
    λ x => if x = 3 then 0 else 1,
    λ x => if x = 4 then 0 else 1,
    λ x => if x = 5 then 0 else 1,
    λ x => if x = 1 then 0 else 1,
    λ x => if x = 0 ∨ x = 1 then 0 else 1,
    λ x => if x = 6 then 0 else 1,
    λ x => if x = 6 ∨ x = 7 then 0 else 1,
    λ x => if x = 0 ∨ x = 7 then 0 else 1
  }

  have aux1(x : Fin 2) : x ≠ 1 → x = 0 := by omega
  have aux2(x y : Fin 2) : (x * y : ℤ) ≤ 1 := by
    fin_cases x <;> fin_cases y <;> simp

  -- Proof that S = T
  have eqS : S = T := by
    apply Finset.ext
    intro a
    constructor
    . intro h
      rw [hS a] at h

      -- There exists at least one zero
      have zero : ∃ k : Fin 8, a k ≠ 1 := by
        by_contra not_zero
        push_neg at not_zero
        have eq1 : a = λ x => 1 := by funext x; simp [not_zero]
        have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) = 7 := by
          simp [eq1]
        rw [h] at this; tauto

      -- enumerate all possible cases
      rcases zero with ⟨k, hk⟩
      apply aux1 at hk
      fin_cases k <;> simp at hk
      . -- case a 0 = 0, here, one must have a 1 or a 7 = 0, others are 1
        cases hh: (a 7).val
        . have (r : Fin 8) (ne07: r ≠ 0 ∧ r ≠ 7): a r = 1 := by
            by_contra not_one
            push_neg at not_one
            apply aux1 at not_one
            have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
              fin_cases r <;> simp at not_one ne07 <;> simp [hk, not_one, hh]
              all_goals (
                try calc
                  _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ = 4 := by norm_num
                try calc
                  _ ≤ (1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ ≤ 4 := by norm_num
              )
            rw [h] at this; tauto
          have in_T : a = (λ x => if x = 0 ∨ x = 7 then 0 else 1) := by
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
          simp [T, in_T]
        . have (r : Fin 8) (ne01: r ≠ 0 ∧ r ≠ 1): a r = 1 := by
            by_contra not_one
            push_neg at not_one
            apply aux1 at not_one
            have a71: a 7 = 1 := by omega
            have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
              fin_cases r <;> simp at not_one ne01 <;> simp [hk, not_one]
              case «7» => rw [a71] at not_one; contradiction
              all_goals (
                try calc
                  _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ = 4 := by norm_num
              )
            rw [h] at this; tauto
          have in_T : a = (λ x => if x = 0 ∨ x = 1 then 0 else 1) := by
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
            by_contra not_zero
            have a11: a 1 = 1 := by omega
            have contra: (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) = 6 := by
              simp [this, a11, hk]
            rw [h] at contra; tauto
          simp [T, in_T]
      . -- case a 1 = 0, here, one have a 0 = 0 or 1, others are 1
        have (r : Fin 8) (ne01: r ≠ 0 ∧ r ≠ 1): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne01 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 0 ∨ x = 1 then 0 else 1) ∨ a = ( λ x => if x = 1 then 0 else 1) := by
          cases hh: (a 0).val
          . left
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
          . right
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
        cases in_T with
        | inl zero2 => simp [T, zero2]
        | inr zero1 => simp [T, zero1]
      . -- case a 2 = 0, here, one must have others are 1
        have (r : Fin 8) (ne2: r ≠ 2): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne2 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 2 then 0 else 1) := by
          funext x; fin_cases x <;> simp
          all_goals (
            try exact this _ (by tauto)
            try exact hk
          )
        simp [T, in_T]
      . -- case a 3 = 0, here, one must have others are 1
        have (r : Fin 8) (ne2: r ≠ 3): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne2 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 3 then 0 else 1) := by
          funext x; fin_cases x <;> simp
          all_goals (
            try exact this _ (by tauto)
            try exact hk
          )
        simp [T, in_T]
      . -- case a 4 = 0, here, one must have others are 1
        have (r : Fin 8) (ne2: r ≠ 4): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne2 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 4 then 0 else 1) := by
          funext x; fin_cases x <;> simp
          all_goals (
            try exact this _ (by tauto)
            try exact hk
          )
        simp [T, in_T]
      . -- csae a 5 = 0, here, one must have others are 1
        have (r : Fin 8) (ne2: r ≠ 5): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne2 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 5 then 0 else 1) := by
          funext x; fin_cases x <;> simp
          all_goals (
            try exact this _ (by tauto)
            try exact hk
          )
        simp [T, in_T]
      . -- case a 6 = 0, here, one must have a 7 = 0 or 1, others are 1
        have (r : Fin 8) (ne01: r ≠ 6 ∧ r ≠ 7): a r = 1 := by
          by_contra not_one
          push_neg at not_one
          apply aux1 at not_one
          have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
            fin_cases r <;> simp at not_one ne01 <;> simp [hk, not_one]
            all_goals (
              try calc
                _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ = 4 := by norm_num
              try calc
                _ ≤ (1 + 1 + 1 : ℤ) := by
                  apply add_le_add; apply add_le_add
                  all_goals exact aux2 (a _) (a _)
                _ ≤ 4 := by norm_num
            )
          rw [h] at this; tauto
        have in_T: a = (λ x => if x = 6 ∨ x = 7 then 0 else 1) ∨ a = ( λ x => if x = 6 then 0 else 1) := by
          cases hh: (a 7).val
          . left
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
          . right
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
        cases in_T with
        | inl zero2 => simp [T, zero2]
        | inr zero1 => simp [T, zero1]
      . -- case a 7 = 0, here, one must have a 6 = 0 or a 0 = 0, others are 1
        cases hh: (a 0).val
        . have (r : Fin 8) (ne07: r ≠ 0 ∧ r ≠ 7): a r = 1 := by
            by_contra not_one
            push_neg at not_one
            apply aux1 at not_one
            have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
              fin_cases r <;> simp at not_one ne07 <;> simp [hk, not_one, hh]
              all_goals (
                try calc
                  _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ = 4 := by norm_num
                try calc
                  _ ≤ (1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ ≤ 4 := by norm_num
              )
            rw [h] at this; tauto
          have in_T : a = (λ x => if x = 0 ∨ x = 7 then 0 else 1) := by
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
          simp [T, in_T]
        . have (r : Fin 8) (ne01: r ≠ 6 ∧ r ≠ 7): a r = 1 := by
            by_contra not_one
            push_neg at not_one
            apply aux1 at not_one
            have a71: a 0 = 1 := by omega
            have : (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) ≤ 4 := by
              fin_cases r <;> simp at not_one ne01 <;> simp [hk, not_one]
              case «0» => rw [a71] at not_one; contradiction
              all_goals (
                try calc
                  _ ≤ (1 + 1 + 1 + 1 : ℤ) := by
                    apply add_le_add; apply add_le_add; apply add_le_add
                    all_goals exact aux2 (a _) (a _)
                  _ = 4 := by norm_num
              )
            rw [h] at this; tauto
          have in_T : a = (λ x => if x = 6 ∨ x = 7 then 0 else 1) := by
            funext x; fin_cases x <;> simp
            all_goals (
              try omega
              try exact hk
              try exact this _ (by tauto)
            )
            by_contra not_zero
            have a61: a 6 = 1 := by omega
            have contra: (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 5 + a 5 * a 6 + a 6 * a 7 : ℤ) = 6 := by
              simp [this, a61, hk]
            rw [h] at contra; tauto
          simp [T, in_T]

    . intro h
      apply (hS a).mpr
      fin_cases h <;> simp
  simp [eqS]; tauto
