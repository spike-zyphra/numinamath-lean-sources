import Mathlib

open Finset

theorem algebra_9096 {f : ℕ → ℕ → ℤ} 
    (hf1 : f 1 1 = 1)
    (hfm : ∀ m n, 0 < m → 0 < n → f (m + 1) n = f m n + 2 * (m + n))
    (hfn : ∀ m n, 0 < m → 0 < n → f m (n + 1) = f m n + 2 * (m + n - 1)) :
    ∀ m n, 0 < m → 0 < n → f m n = (m + n) ^ 2 - m - 3 * n + 1 := by
  intro m n hm hn
  have h11 : ∀ m n : ℕ, 0 < m → 0 < n → f m n = (m + n) ^ 2 - m - 3 * n + 1 := by
    intro m n hm hn
    have h12 : ∀ k : ℕ, ∀ m n : ℕ, m + n = k + 2 → 0 < m → 0 < n → f m n = (m + n) ^ 2 - m - 3 * n + 1 := by
      intro k 
      induction k with 
      | zero =>
        intro m n h h1 h2
        have hmn1 : m = 1 := by
          omega
        have hmn2 : n = 1 := by
          omega
        rw [hmn1, hmn2]
        simp [hf1]
        all_goals omega
      | succ k ih =>
        intro m n h h1 h2
        have h3 : m + n = k + 1 + 2 := by 
          omega
        have h4 : m + n - 1 = k + 2 := by 
          omega
        by_cases h12 : m ≤ 1 
        · -- m = 1
          have hm1 : m = 1 := by 
            omega 
          have hn1 : n = k + 2 := by 
            omega 
          rw [hm1, hn1]
          have h2 : f 1 (k + 2) = f 1 (k + 1) + 2 * (1 + (k + 1) - 1 : ℤ) := by 
            specialize hfn 1 (k + 1) (by norm_num) (by omega)
            simpa using hfn
          rw [h2]
          have h4 : f 1 (k + 1) = (1 + (k + 1 : ℕ)) ^ 2 - 1 - 3 * (k + 1 : ℕ) + 1 := by 
            apply ih 
            · -- Show (m' + n' = k + 2)
              omega 
            all_goals 
              omega 
          rw [h4] 
          simp [add_mul, mul_add, pow_two] at *
          <;> ring_nf at *
          all_goals 
            omega 
        · -- m > 1
          have hm3 : m > 1 := by 
            omega 
          have hm22 : m - 1 > 0 := by
            omega
          have hn22 : n > 0 := by
            omega
          have eq1 : f m n = f (m - 1) n + 2 * ((m - 1 : ℕ) + (n : ℕ) ) := by
            have h13 : f m n = f (m - 1 + 1) n := by 
              rw [show m - 1 + 1 = m by omega]
            rw [h13]
            specialize hfm (m - 1) n (by omega) (by omega)
            simpa using hfm
          rw [eq1]
          have h5 : f (m - 1) n = ((m - 1 : ℕ) + (n : ℕ)) ^ 2 - (m - 1 : ℕ) - 3 * (n : ℕ) + 1 := by
            apply ih 
            · -- Show (m' + n' = k + 2)
              omega 
            all_goals 
              omega 
          rw [h5]
          cases m with 
          | zero => 
            exfalso 
            omega
          | succ m => 
            cases m with 
            | zero => 
              exfalso
              omega
            | succ m => 
              simp [add_mul, mul_add, pow_two] at *
              all_goals 
                ring_nf at *
                all_goals 
                  omega 
    specialize h12 (m + n - 2) m n (by omega) hm hn 
    simpa using h12 
  specialize h11 m n hm hn 
  simpa using h11