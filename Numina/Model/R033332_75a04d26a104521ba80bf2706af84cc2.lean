import Mathlib

theorem algebra_109800 {x : ℝ} (hx : ∃ n : ℤ, x + 1/x = n) (n : ℕ) :
    ∃ m : ℤ, x^n + 1/x^n = m := by
  rcases hx with ⟨m_val, hm⟩
  by_cases h1 : x = 0
  · -- Case where x = 0
    rw [h1] at hm
    have hm2 : (0 : ℝ) + (1 / (0 : ℝ)) = (m_val : ℝ) := hm
    have : m_val = 0 := by 
      norm_num at hm2 ⊢
      all_goals try { 
        have : (m_val : ℝ) = (0 : ℝ) := by nlinarith 
        norm_cast at this ⊢
      }
      <;> try { tauto }
      <;> try { nlinarith }
    rw [h1]
    cases n with
    | zero =>
      use 2
      norm_num
      <;> try { tauto }
      <;> try { nlinarith }
    | succ n =>
      use (0 : ℤ)
      have h_zero : (0 : ℝ) ^ (n + 1 : ℕ) = (0 : ℝ) := by 
        simp
        <;> try { tauto }
        <;> try { nlinarith }
      have h_zero2 : 1 / ((0 : ℝ) ^ (n + 1 : ℕ)) = (0 : ℝ) := by
        rw [h_zero]
        norm_num
        all_goals try { tauto }
        <;> try { nlinarith }
      simp [h_zero, h_zero2]
      all_goals norm_num
      all_goals try { tauto }
      all_goals try { nlinarith }
      all_goals try { 
        nlinarith 
      }
      <;> try { tauto }
      <;> try { nlinarith }
  · -- Case where x ≠ 0 
    have hx2 : x ≠ 0 := h1 
    have h2 : ∀ n : ℕ, ∃ k : ℤ, x ^ n + 1 / x ^ n = k := by 
      intro n 
      induction' n using Nat.strongRecOn with n ih 
      cases n with 
      | zero =>
        use 2 
        norm_num 
      | succ n =>
        cases n with 
        | zero =>
          use m_val 
          field_simp [hx2] at *
          all_goals try nlinarith 
          all_goals try { trivial }
        | succ n =>
          rcases ih (n) (by linarith) with ⟨k, hk⟩
          rcases ih (n + 1) (by linarith) with ⟨l, hl⟩
          use l * m_val - k
          have h_eq1 : x ^ (n + 2 : ℕ) + 1 / x ^ (n + 2 : ℕ) = (x ^ (n + 1 : ℕ) + 1 / x ^ (n + 1 : ℕ)) * (x + 1 / x) - (x ^ (n : ℕ) + 1 / x ^ (n : ℕ)) := by 
            field_simp [hx2]
            <;> ring_nf 
            <;> field_simp [hx2] 
            all_goals linarith 
            all_goals try { tauto }
          rw [h_eq1, hl, hk, hm]
          all_goals try { norm_num }
          <;> ring_nf 
          <;> norm_num 
          all_goals try { linarith }
          all_goals try { tauto }
        all_goals try { linarith }
        all_goals try { tauto }
      all_goals try { linarith }
      all_goals try { tauto }
    specialize h2 n 
    rcases h2 with ⟨k, hk⟩ 
    exact ⟨k, hk⟩