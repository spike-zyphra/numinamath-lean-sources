import Mathlib

theorem number_theory_219784 (n : ℕ) :
    ∃ m : ℤ, (2 / (3 + Real.sqrt 5))^n + ((3 + Real.sqrt 5) / 2)^n = m := by 
  have h1 : ∀ n : ℕ, ∃ m : ℤ, (2 / (3 + Real.sqrt 5))^n + ((3 + Real.sqrt 5) / 2)^n = m := by
    intro n 
    have h2 : (2 / (3 + Real.sqrt 5) : ℝ) = (3 - Real.sqrt 5) / 2 := by
      field_simp [(show 3 + Real.sqrt 5 ≠ 0 by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      )]
      <;> ring_nf <;> norm_num
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [show (2 / (3 + Real.sqrt 5) : ℝ) = (3 - Real.sqrt 5) / 2 by linarith [h2]]
    have h3 : ∀ (n : ℕ), ∃ (m : ℤ), ((3 - Real.sqrt 5) / 2 : ℝ)^n + ((3 + Real.sqrt 5) / 2)^n = m := by
      intro n 
      induction' n using Nat.strongRecOn with n ih 
      cases n with
      | zero =>
        use 2
        norm_num
      | succ n =>
        cases n with
        | zero =>
          use 3
          field_simp 
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        | succ n =>
          rcases ih (n + 1) (by linarith) with ⟨m1, hm1⟩
          rcases ih (n) (by linarith) with ⟨m2, hm2⟩
          use 3 * m1 - m2
          have eq1 : ((3 - Real.sqrt 5) / 2 : ℝ) ^ (n + 2) + ((3 + Real.sqrt 5) / 2 : ℝ) ^ (n + 2) = 3 * (((3 - Real.sqrt 5) / 2 : ℝ) ^ (n + 1) + ((3 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1)) - (( (3 - Real.sqrt 5) / 2 : ℝ) ^ n + ((3 + Real.sqrt 5) / 2 : ℝ) ^ n) := by
            ring_nf
            <;> simp [pow_two, pow_succ, mul_add, mul_sub]
            <;> ring_nf
            <;> norm_num 
          rw [eq1]
          rw [hm1]
          rw [hm2]
          all_goals norm_num
          all_goals ring
    exact h3 n 
  exact h1 n