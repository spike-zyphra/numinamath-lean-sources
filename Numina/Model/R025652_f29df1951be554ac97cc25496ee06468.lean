import Mathlib

theorem algebra_7947 {a b : ℤ} (h : (a - 1)^2 + |b + 1| = 1) :
    (a = 2 ∧ b = -1) ∨ (a = 0 ∧ b = -1) ∨ (a = 1 ∧ b = -2) ∨ (a = 1 ∧ b = 0) := by
  have h1 : (a - 1) ^ 2 ≤ 1 := by 
    have h2 : |b + 1| ≥ 0 := by apply abs_nonneg
    nlinarith
  have h2 : |b + 1| ≤ 1 := by
    have h1' : (a - 1) ^ 2 ≥ 0 := by nlinarith
    nlinarith
  have h1' : (a - 1) ^ 2 = 0 ∨ (a - 1) ^ 2 = 1 := by 
    have h11 : (a - 1) ^ 2 ≤ 1 := h1
    have h12 : (a - 1) ^ 2 ≥ 0 := by nlinarith
    have h13 : (a - 1) ^ 2 ≤ 1 := by linarith
    have h14 : (a - 1) ^ 2 ≥ 0 := by nlinarith
    have : (a - 1) ^ 2 = 0 ∨ (a - 1) ^ 2 = 1 := by 
      have h14 : (a - 1) ^ 2 ≤ 1 := by linarith
      have h15 : (a - 1) ^ 2 ≥ 0 := by nlinarith
      interval_cases (a - 1) ^ 2 <;> tauto
    assumption
  have h4 : |b + 1| = 0 ∨ |b + 1| = 1 := by 
    have h11 : |b + 1| ≤ 1 := h2
    have h12 : |b + 1| ≥ 0 := by apply abs_nonneg
    have h13 : |b + 1| ≤ 1 := by linarith
    have h14 : |b + 1| ≥ 0 := by apply abs_nonneg
    have : |b + 1| = 0 ∨ |b + 1| = 1 := by
      have h14 : |b + 1| ≤ 1 := by linarith
      have h15 : |b + 1| ≥ 0 := by apply abs_nonneg
      interval_cases |b + 1| <;> tauto
    assumption
  rcases h1' with h1' | h1'
  · -- Case (a - 1)^2 = 0
    rcases h4 with h4 | h4 
    · -- Case (a - 1)^2 = 0 and |b + 1| = 0
      have h3 : (a - 1) ^ 2 = 0 := h1'
      have h3' : a - 1 = 0 := by 
        nlinarith
      have h4' : |b + 1| = 0 := h4
      have h5 : b + 1 = 0 := by 
        rw [abs_eq_zero] at h4'
        linarith 
      have h5' : b = -1 := by 
        linarith
      have h6 : a = 1 := by
        linarith 
      exfalso
      rw [h6, h5'] at h 
      norm_num [abs] at h 
      <;> linarith 
    · -- Case (a - 1)^2 = 0 and |b + 1| = 1
      have h3 : (a - 1) ^ 2 = 0 := h1'
      have h3' : a - 1 = 0 := by 
        nlinarith 
      have h4' : |b + 1| = 1 := h4 
      have h9 : b + 1 = 1 ∨ b + 1 = -1 := by 
        cases' eq_or_eq_neg_of_abs_eq h4' with h9 h10 
        · -- case b + 1 = 1
          left
          linarith 
        · -- case b + 1 = -1
          right
          linarith 
      have h8 : a = 1 := by
        linarith 
      cases h9 with
      | inl h10 =>
        -- Now we need to show that from these hypotheses, the goal is provable:
        -- This is (a,b)=(1,0)
        have h10' : b = 0 := by
          linarith 
        simp [h8, h10'] 
      | inr h11 =>
        -- This is (a,b)=(1,-2)
        have h11' : b = -2 := by 
          linarith 
        simp [h8, h11'] 
  · -- Case (a - 1)^2 = 1
    rcases h4 with h4 | h4
    · -- Case (a - 1)^2 = 1 and |b + 1| = 0
      have h3 : (a - 1) ^ 2 = 1 := h1'
      have h6 : a - 1 = 1 ∨ a - 1 = -1 := by
        have h7 : (a - 1) ^ 2 = 1 := h3 
        have : a - 1 = 1 ∨ a - 1 = -1 := by 
          rw [sq_eq_one_iff] at h7 
          tauto 
        assumption 
      have h4' : |b + 1| = 0 := h4 
      have h7 : b + 1 = 0 := by 
        rw [abs_eq_zero] at h4' 
        linarith 
      have h8 : b = -1 := by 
        linarith 
      cases h6 with
      | inl h8a =>
        have h9 : a = 2 := by 
          linarith 
        simp [h9, h8] 
      | inr h8a =>
        -- Now we need to show that from h8a a-1 = -1, ..., the goal is valid
        have h9 : a = 0 := by 
          linarith 
        simp [h9, h8] 
    · -- Case (a - 1)^2 = 1 and |b + 1| = 1
      -- This introduces four possible pairs that we need to show are invalid or valid per goal
      have h3 : (a - 1) ^ 2 = 1 := h1'
      have h6 : a - 1 = 1 ∨ a - 1 = -1 := by 
        have h7 : (a - 1) ^ 2 = 1 := h3 
        have : a - 1 = 1 ∨ a - 1 = -1 := by 
          rw [sq_eq_one_iff] at h7 
          tauto 
        assumption 
      have h4' : |b + 1| = 1 := h4 
      have h8 : b + 1 = 1 ∨ b + 1 = -1 := by 
        cases' eq_or_eq_neg_of_abs_eq h4' with h9 h10 
        · -- case b + 1 = 1
          left 
          linarith 
        · -- case b + 1 = -1
          right 
          linarith 
      cases h6 with
      | inl h8a =>
        have h9 : a = 2 := by 
          linarith 
        cases h8 with 
        | inl h11 => 
          -- Now we need to show that (a,b)=(2,0) contradicts h
          exfalso 
          have h12 : b = 0 := by 
            linarith 
          have h13 : (a - 1) ^ 2 + |b + 1| = 2 := by 
            rw [h9, h12] 
            norm_num [abs] 
          linarith 
        | inr h11 => 
          -- Similarly for (2, -2)
          exfalso 
          have h12 : b = -2 := by 
            linarith 
          have h13 : (a - 1) ^ 2 + |b + 1| = 2 := by 
            rw [h9, h12] 
            norm_num [abs] 
          linarith 
      | inr h8a => 
        -- Now a=0
        have h9 : a = 0 := by 
          linarith 
        cases h8 with 
        | inl h11 => 
          -- Now (a,b)=(0,0) must contradict h
          exfalso 
          have h12 : b = 0 := by 
            linarith 
          have h13 : (a - 1) ^ 2 + |b + 1| = 2 := by 
            rw [h9, h12] 
            norm_num [abs] 
          linarith 
        | inr h11 => 
          -- Similarly, (0, -2)
          exfalso 
          have h12 : b = -2 := by 
            linarith 
          have h13 : (a - 1) ^ 2 + |b + 1| = 2 := by 
            rw [h9, h12] 
            norm_num [abs] 
          linarith