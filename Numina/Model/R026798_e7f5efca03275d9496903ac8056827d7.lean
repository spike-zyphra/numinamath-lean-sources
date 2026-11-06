import Mathlib

theorem algebra_1646 {a b c : ℤ} (h : Odd (a + b + c)) :
  Odd (a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b) := by
  have h1 : (a + b + c : ℤ) % 2 = 1 := by
    rcases h with ⟨k, hk⟩
    omega
  have h2 : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by
    omega
  cases h2 with
  | inl h20 =>
    have h3 : c % 2 = 1 := by
      omega
    have h4 : (a % 2 = 0 ∧ b % 2 = 0) ∨ (a % 2 = 1 ∧ b % 2 = 1) := by
      omega
    cases h4 with
    | inl h41 =>
      have ha : a % 2 = 0 := h41.left
      have hb : b % 2 = 0 := h41.right
      -- Now compute the expression mod 2
      have h5 : (a ^ 2) % 2 = 0 := by
        simp [ha, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      have h6 : (b ^ 2) % 2 = 0 := by
        simp [hb, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      have h7 : (c ^ 2) % 2 = 1 := by
        simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      have h8 : (2 * a * b) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      -- Show the entire expression is 1 mod 2
      have h9 : (a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b) % 2 = 1 := by
        omega
      exact ⟨(a^2 + b ^ 2 - c ^ 2 + 2 * a * b) / 2, by omega⟩
    | inr h42 =>
      have ha : a % 2 = 1 := h42.left
      have hb : b % 2 = 1 := h42.right
      -- Now compute the expression mod 2
      have h5 : (a ^ 2) % 2 = 1 := by
        simp [ha, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h6 : (b ^ 2) % 2 = 1 := by
        simp [hb, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h7 : (c ^ 2) % 2 = 1 := by
        simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h8 : (2 * a * b) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      -- Show the entire expression is 1 mod 2
      have h9 : (a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b) % 2 = 1 := by
        omega
      exact ⟨(a^2 + b ^ 2 - c ^ 2 + 2 * a * b) / 2, by omega⟩
  | inr h21 =>
    have h3 : c % 2 = 0 := by
      omega
    -- Need to check all combinations where a + b is odd
    have h4 : (a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0) := by
      omega
    cases h4 with
    | inl h41 =>
      have ha : a % 2 = 0 := h41.left
      have hb : b % 2 = 1 := h41.right
      -- Now compute the expression mod 2
      have h5 : (a ^ 2) % 2 = 0 := by
        simp [ha, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h6 : (b ^ 2) % 2 = 1 := by
        simp [hb, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h7 : (c ^ 2) % 2 = 0 := by
        simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h8 : (2 * a * b) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      -- Show the entire expression is 1 mod 2
      have h9 : (a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b) % 2 = 1 := by
        omega
      exact ⟨(a^2 + b ^ 2 - c ^ 2 + 2 * a * b) / 2, by omega⟩
    | inr h42 =>
      have ha : a % 2 = 1 := h42.left
      have hb : b % 2 = 0 := h42.right
      -- Now compute the expression mod 2
      have h5 : (a ^ 2) % 2 = 1 := by
        simp [ha, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h6 : (b ^ 2) % 2 = 0 := by
        simp [hb, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h7 : (c ^ 2) % 2 = 0 := by
        simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      have h8 : (2 * a * b) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, Int.sub_emod]
        all_goals omega
      -- Show the entire expression is 1 mod 2
      have h9 : (a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b) % 2 = 1 := by
        omega
      exact ⟨(a^2 + b ^ 2 - c ^ 2 + 2 * a * b) / 2, by omega⟩