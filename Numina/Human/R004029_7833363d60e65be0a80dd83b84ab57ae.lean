import Mathlib

/-Susie thinks of a positive integer $n$. She notices that, when she divides 2023 by $n$, she is left with a remainder of 43 . Find how many possible values of $n$ there are.-/
theorem number_theory_231458 : {n : ℕ | 0 < n ∧ 2023 % n = 43}.encard = 19 := by
  -- Define set S as the set of natural numbers satisfying the condition
  let S := {n : ℕ | 0 < n ∧ 2023 % n = 43}

  -- Define finite set S0, containing all 19 numbers that satisfy the condition
  let S0:Finset ℕ :={1980, 990, 660, 495,396,330,220,198,180,165,132,110,99,90,66,60,55,45,44}

  -- Prove that set S equals finite set S0
  have h1:S=S0:=by
    refine Set.ext ?_
    intro x
    constructor

    -- Prove that all elements in S are in S0
    · intro hx
      simp[S] at hx
      obtain⟨h2,h3⟩:=hx

      -- Prove x ≥ 44 using the fact that 2023 % x = 43 < x
      have h6: x≥44:=by
        have :2023%x<x:= Nat.mod_lt 2023 h2
        omega
      have h2:(2023-43)%x=0:=by
        refine Nat.sub_mod_eq_zero_of_mod_eq ?_
        have : 43%x=43:=by exact Nat.mod_eq_of_lt h6
        omega
      -- Show that x divides 1980
      have h3:x∣1980:=by
        norm_num at h2
        exact Nat.dvd_of_mod_eq_zero h2
      have h4:x∈Nat.divisors 1980:=by
        apply Nat.mem_divisors.mpr
        tauto
      -- Use the fact that divisors of 1980 are exactly the elements in S0
      have h5:Nat.divisors 1980={1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 15, 18, 20, 22, 30, 33, 36, 44,
              45, 55, 60, 66, 90, 99, 110, 132, 165, 180, 198, 220, 330, 396,
              495, 660, 990, 1980}:=by
        native_decide
      rw[h5] at h4
      fin_cases h4
      all_goals
      norm_num at h6
      try native_decide

    -- Prove that all elements in S0 are in S (verify each number satisfies the condition)
    · intro hx
      simp [S0] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                           rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
      constructor
      · norm_num  -- Verify each number is greater than 0
      · norm_num  -- Verify the remainder when each number divides 2023 is 43

  -- Since S=S0 and S0 is finite, the cardinality of S equals the number of elements in S0
  have h2:S.encard=S0.card:=by
    rw[h1]
    exact Set.encard_coe_eq_coe_finsetCard S0

  -- Complete the proof (S0 contains 19 elements)
  tauto
