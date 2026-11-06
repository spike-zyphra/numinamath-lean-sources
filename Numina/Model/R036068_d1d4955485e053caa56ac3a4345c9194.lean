import Mathlib

theorem algebra_235094 (a : ℕ → ℤ) (ha : a 0 = -1 ∧ a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 3)
    (h : ∀ n, a (n + 5) = a n * a (n + 1)) :
    a 12 = 12 ∧ ∀ n, n ≥ 13 → a n = 0:= by 
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  have ha5 : a 5 = 0 := by 
    specialize h 0 
    norm_num [ha0, ha1] at h ⊢ 
    linarith 
  have ha6 : a 6 = 0 := by
    specialize h 1 
    norm_num [ha1, ha2] at h ⊢ 
    linarith 
  have ha7 : a 7 = 2 := by 
    specialize h 2
    norm_num [ha2, ha3] at h ⊢ 
    linarith 
  have ha8 : a 8 = 6 := by 
    specialize h 3 
    norm_num [ha3, ha4] at h ⊢ 
    linarith 
  have ha9 : a 9 = 0 := by 
    specialize h 4 
    norm_num [ha4, ha5] at h ⊢ 
    linarith 
  have ha10 : a 10 = 0 := by 
    specialize h 5 
    norm_num [ha5, ha6] at h ⊢ 
    linarith 
  have ha11 : a 11 = 0 := by 
    specialize h 6 
    norm_num [ha6, ha7] at h ⊢ 
    linarith 
  have ha12 : a 12 = 12 := by 
    specialize h 7 
    norm_num [ha7, ha8] at h ⊢ 
    linarith 
  constructor 
  · exact ha12
  · intro n hn
    have h313 : ∀ (m : ℕ), a (m + 13) = 0 := by
      intro m
      induction' m using Nat.strongRecOn with m ih
      cases m with 
      | zero => 
        have h13 : a 13 = 0 := by
          have h8 : a 13 = a 8 * a 9 := by
            specialize h 8 
            simpa using h 
          rw [h8]
          all_goals 
            rw [ha8, ha9]
            all_goals 
              norm_num 
        simpa using h13 
      | succ m => 
        cases m with 
        | zero => 
          have h14 : a 14 = 0 := by 
            have h910 : a 14 = a 9 * a 10 := by 
              specialize h 9 
              simpa using h 
            rw [h910]
            all_goals 
              rw [ha9, ha10]
              all_goals 
                norm_num 
          simpa using h14 
        | succ m => 
          cases m with 
          | zero => 
            have h15 : a 15 = 0 := by 
              have h1011 : a 15 = a 10 * a 11 := by 
                specialize h 10 
                simpa using h 
              rw [h1011]
              all_goals 
                rw [ha10, ha11]
                all_goals 
                  norm_num 
            simpa using h15 
          | succ m => 
            cases m with 
            | zero => 
              have h16 : a 16 = 0 := by 
                have h1112 : a 16 = a 11 * a 12 := by 
                  specialize h 11 
                  simpa using h 
                rw [h1112]
                all_goals 
                  rw [ha11, ha12]
                  all_goals 
                    norm_num 
              simpa using h16 
            | succ m => 
              cases m with 
              | zero => 
                have h17 : a 17 = 0 := by 
                  have h1213 : a 17 = a 12 * a 13 := by 
                    specialize h 12 
                    simpa using h 
                  rw [h1213]
                  all_goals 
                    rw [ha12]
                    <;> have h13 : a 13 = 0 := by 
                      have h8 : a 13 = a 8 * a 9 := by 
                        specialize h 8 
                        simpa using h 
                      rw [h8]
                      all_goals 
                        rw [ha8, ha9]
                        all_goals 
                          norm_num 
                    rw [h13]
                    all_goals 
                      norm_num 
                simpa using h17 
              | succ m => 
                have eq1 : a (m + 18) = a (m + 13) * a (m + 14) := by 
                  specialize h (m + 13) 
                  simpa using h 
                have eq2 : a (m + 13) = 0 := by 
                  apply ih (m) 
                  all_goals 
                    omega 
                rw [eq1]
                rw [eq2]
                all_goals 
                  norm_num 
    have eq9 : n - 13 + 13 = n := by omega 
    have h313 : ∀ (m : ℕ), a (m + 13) = 0 := h313
    have eq34 : a n = 0 := by 
      have eq35 : a (n - 13 + 13) = 0 := by 
        apply h313 (n - 13)
      rw [eq9] at eq35 
      linarith 
    exact_mod_cast eq34