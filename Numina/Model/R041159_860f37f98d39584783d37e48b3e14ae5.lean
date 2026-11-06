import Mathlib

theorem number_theory_253344 (n : ℕ) :
    8 ∣ 6 * n^2 + 4 * n + (-1 : ℤ)^n * 9 + 7 := by
  have h3 : ∀ n : ℕ, (8 : ℤ) ∣ 6 * (n : ℤ)^2 + 4 * (n : ℤ) + (-1 : ℤ)^n * 9 + 7 := by
    intro n
    have h4 : (n : ℕ) % 2 = 0 ∨ (n : ℕ) % 2 = 1 := by omega
    rcases h4 with (h | h)
    · -- n is even
      have h5 : (n : ℕ) % 2 = 0 := h
      have h6 : ∃ k : ℕ, n = 2 * k := by 
        refine ⟨n / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      have h8 : ((-1 : ℤ) : ℤ) ^ n = 1 := by
        rw [show n = 2 * k by linarith [hk]]
        have h9 : ∀ (k : ℕ), ((-1 : ℤ) : ℤ) ^ (2 * k) = 1 := by 
          intro k
          induction k with
          | zero => 
            norm_num
          | succ k ih =>
            simp [pow_mul, pow_add, pow_two] at ih ⊢
            all_goals linarith
        exact h9 k
      rw [h8]
      rw [show (n : ℤ) = (2 * (k : ℤ) : ℤ) by exact_mod_cast (show (n) = 2 * k by linarith [hk] : (n) = 2 * k)]
      ring_nf at *
      omega
    · -- n is odd
      have h7 : (n : ℕ) % 2 = 1 := h
      have h8 : ∃ k : ℕ, n = 2 * k + 1 := by 
        refine ⟨(n - 1) / 2, by omega⟩
      rcases h8 with ⟨k, hk⟩
      have h10 : ((-1 : ℤ) : ℤ) ^ n = -1 := by
        rw [show n = 2 * k + 1 by linarith [hk]]
        have h11 : ∀ k : ℕ, ((-1 : ℤ) : ℤ) ^ (2 * k + 1) = -1 := by 
          intro k
          induction k with
          | zero => 
            norm_num
          | succ k ih =>
            simp [pow_add, pow_mul, pow_two] at ih ⊢
            all_goals linarith
        exact h11 k
      rw [h10]
      rw [show (n : ℤ) = (2 * (k : ℤ) + 1 : ℤ) by exact_mod_cast (show (n) = 2 * k + 1 by linarith [hk] : (n) = 2 * k + 1)]
      ring_nf at *
      omega
  specialize h3 n
  simpa using h3