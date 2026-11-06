import Mathlib

theorem number_theory_126641 (n k : ℕ) :
    2023 + 2 ^ n = k ^ 2 ↔ (n = 1 ∧ k = 45) := by
  constructor
  · -- Assume 2023 + 2^n = k^2, prove (n = 1 ∧ k = 45)
    intro h
    have h1 : k ^ 2 = 2023 + 2 ^ n := by
      linarith 
    by_cases h2 : n < 3
    · -- Assume n < 3, so n = 0, 1, or 2.
      interval_cases n <;> try { 
        norm_num at h1
        all_goals
          try { 
            have h2 : k ≤ 50 := by nlinarith 
            interval_cases k <;> omega 
          } <;> try { 
            all_goals nlinarith 
          }
      }
    · -- Assume n ≥ 3.
      have h3 : n ≥ 3 := by omega
      have h4 : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by 
        have h1 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by 
          omega 
        rcases h1 with (h | h | h | h | h | h | h | h) <;> 
          simp [pow_two, Nat.mul_mod, h] 
      -- Let's compute the residues of the right side. The right side is $2023 + 2^n$.
      -- $2023 \equiv 7 \mod 8$
      -- And for $2^n$ with $n \geq 3$, we have $2^n \equiv 0 \mod 8$:
      have h5 : (2023 + 2 ^ n) % 8 = 7 := by
        have h6 : n ≥ 3 := h3 
        have h7 : (2 ^ n : ℕ) % 8 = 0 := by 
          have h8 : ∀ m, (2 ^ (m + 3) : ℕ) % 8 = 0 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              simp [pow_add, pow_mul] at ih ⊢ 
              all_goals 
                omega 
          specialize h8 (n - 3) 
          have h9 : n - 3 + 3 = n := by 
            omega 
          rw [h9] at h8 
          exact h8 
        omega 
      -- Thus contradiction
      have h8 : k ^ 2 = 2023 + 2 ^ n := by 
        linarith 
      have h9 : k ^ 2 % 8 = 7 := by 
        omega 
      omega 
  · -- Assume n = 1 ∧ k = 45, prove 2023 + 2^n = k^2
    rintro ⟨hn, hk⟩
    rw [hn, hk]
    all_goals 
      norm_num