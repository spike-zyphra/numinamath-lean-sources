import Mathlib

theorem algebra_227921 (M : ℝ) (hM : M > 0)  -- 总重量M > 0 
  (h1 : (35 / 100 : ℝ) * M = 0.35 * M)  -- 最大的三条鱼重量为35%M
  (h2 : (5 / 13 : ℝ) * (M - 0.35 * M) = 0.25 * M) -- 三条最小鱼重量为剩余重量的5/13，即0.25M
  (h3 : 0.35 * M / 3 ≥ 0.4 * M / (n - 6))  -- 最大鱼平均重量 ≥ 午餐鱼平均重量 
  (h4 : 0.4 * M / (n - 6) ≥ 0.25 * M / 3) :  -- 午餐鱼平均重量 ≥ 最小鱼平均重量 
  {n : ℕ | 0.35 * M / 3 ≥ 0.4 * M / (n - 6) ∧ 0.4 * M / (n - 6) ≥ 0.25 * M / 3} = {10} :=by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First: show from hypotheses that n =10
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h5 : (n : ℝ) - 6 > 0
    · -- Then n - 6 >0.
      have h6 : (n : ℝ) > 6 := by
        by_contra h
        push_neg at h
        have : (n : ℝ) ≤ 6 := by linarith
        have : (n : ℝ) - 6 ≤ 0 := by linarith
        linarith
      -- Divide inequalities by M >0
      have h7 : (0.35 * M / 3) ≥ (0.4 * M / (n - 6 : ℝ)) := h1
      have h8 : (0.35 * M / 3) / M ≥ (0.4 * M / (n - 6 : ℝ)) / M := by
        apply (div_le_div_right hM).mpr
        exact h7
      have h9 : (0.35 / 3 : ℝ) ≥ (0.4 / (n - 6 : ℝ)) := by
        have h10 : (0.35 * M / 3) / M = (0.35 / 3 : ℝ) := by
          field_simp
          <;> linarith
        have h11 : (0.4 * M / (n - 6 : ℝ)) / M = (0.4 / (n - 6 : ℝ) : ℝ) := by
          field_simp
          <;> linarith
        linarith [h10, h11, h8]
      -- Derive≥ from h4
      have h10 : (0.4 / (n - 6 : ℝ) ) ≥ (0.25 / 3 : ℝ) := by
        have h12 : (0.4 * M / (n - 6 : ℝ) ) ≥ (0.25 * M / 3) := h2
        have h13 : (0.4 * M / (n - 6 : ℝ) ) / M ≥ (0.25 * M / 3) / M := by
          apply (div_le_div_right hM).mpr
          exact h12
        have h14 : (0.4 / (n - 6 : ℝ) : ℝ) ≥ (0.25 / 3 : ℝ) := by
          have h15 : (0.4 * M / (n - 6 : ℝ)) / M = (0.4 / (n - 6 : ℝ) : ℝ) := by
            field_simp
            <;> linarith
          have h16 : (0.25 * M / 3) / M = (0.25 / 3 : ℝ) := by
            field_simp
            <;> linarith
          linarith [h15, h16, h13]
        linarith
      -- Use algebra to bound n.
      have h11 : n = 10 := by
        by_contra h
        push_neg at h
        have h12 : n < 10 ∨ n > 10 := by
          omega
        cases h12 with
        | inl h13 =>
          have h14 : n ≤ 9 := by
            omega
          have h15 : (n : ℝ) ≤ (9 : ℝ) := by
            exact_mod_cast h14
          have h16 : (n - 6 : ℝ) ≤ (3 : ℝ) := by
            nlinarith
          have h17 : (0.35 / (3 : ℝ) ) ≥ (0.4 / (n - 6 : ℝ)) := by
            linarith [h9]
          have h18 : (0.4 / (n - 6 : ℝ) ) ≥ (0.25 / (3 : ℝ) ) := by
            linarith [h10]
          interval_cases n <;> norm_num at h17 h18 <;> norm_num at *
          <;> try { linarith }
          <;> try { tauto }
        | inr h14 =>
          -- this part for n>10, contradiction.
          have h15 : n ≥ 11 := by
            omega
          have h16 : (n : ℝ) ≥ (11 : ℝ) := by
            exact_mod_cast h15
          -- Derive contradiction
          have h21 : (n - 6 : ℝ) ≥ (5 : ℝ) := by
            have h22 : (n : ℝ) ≥ (11 : ℝ) := by
              exact_mod_cast h16
            linarith
          have h23 : (n : ℝ) ≤ (10.8 : ℝ) := by
            by_contra h
            push_neg at h
            have h24 : (n : ℝ) > (10.8 : ℝ) := h
            have h25 : (n - 6 : ℝ) > (4.8 : ℝ) := by
              linarith
            -- Manipulate h10 for contradiction
            have h26 : (0.4 / (n - 6 : ℝ)) < (0.25 / 3 : ℝ) := by
              have h27 : (n - 6 : ℝ) > (0 : ℝ) := by nlinarith
              have h28 : (0.4 / (n - 6 : ℝ)) < (0.25 / 3 : ℝ) := by
                have h31 : (n - 6 : ℝ) > (4.8 : ℝ) := h25
                have h32 : (0.4 / (n - 6 : ℝ) ) < (0.25 / 3 : ℝ) := by
                  have h33 : (n - 6 : ℝ) > (0 : ℝ) := by nlinarith
                  apply (div_lt_div_iff (by linarith) (by linarith)).mpr
                  nlinarith
                assumption
              assumption
            linarith [h10, h26]
          have h23 : n ≤ 10 := by
            by_contra h
            push_neg at h
            have h24 : n ≥ 11 := by
              omega
            have h25 : (n : ℝ) ≥ (11 : ℝ) := by
              exact_mod_cast h24
            nlinarith
          linarith
      exact_mod_cast h11
    · -- If h5 not, n -6 <=0.
      have h6 : (n : ℝ) - 6 ≤ (0 : ℝ) := by
        by_contra h
        push_neg at h
        have h5' : (n : ℝ) - 6 > 0 := by nlinarith
        linarith
      have h6' : (n : ℝ) ≤ (6 : ℝ) := by linarith
      have h11 : n ≤ 6 := by
        by_contra h
        push_neg at h
        have h12 : n ≥ 7 := by omega
        have h13 : (n : ℝ) ≥ (7 : ℝ) := by
          exact_mod_cast h12
        nlinarith
      interval_cases n <;> norm_num at h1 h2 <;> norm_num at *
      <;> try { linarith }
      <;> try { tauto }
  · -- Show that n =10 satisfy all constraints.
    intro h
    rw [h]
    constructor
    · -- Show that n =10 satisfy first constraint
      norm_num
      <;> try { linarith }
      <;> try { tauto }
    · -- Show that n =10 satisfy second constraint
      norm_num
      <;> try { linarith }
      <;> try { tauto }