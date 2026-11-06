import Mathlib

theorem number_theory_96796 (f : ℕ → ℕ → ℕ)
(h₀ : ∀ i j, i = 0 → j ≤ 4 → f i j = (j + 1)%5)
(h₁ : ∀ i j, i ≥ 1 → j = 0 → f i j = f (i - 1) 1)
(h₂ : ∀ i j, i ≥ 1 → 1 ≤ j ∧ j ≤ 4 → f i j = f (i - 1) (f i (j - 1))) :f 2015 2 = 1 := by
  have mainthm (i :ℕ) (hi:5≤ i):∀j, (jle4:j≤4) → f i j= 1:=by
    induction' i,hi using Nat.le_induction with k kge5
    · intro j jle4
      interval_cases j
      all_goals simp[h₁,h₂,h₀]
    · rename_i hk
      intro j jle4
      -- Given kge5 and hk (which states is value for k).
      -- We need to compute value for k+1.
      have h10 : f k 0 = 1 := by
        have hk' : ∀ j, j ≤ 4 → f k j = 1 := by
          simpa using hk
        specialize hk' 0 (by omega)
        simpa using hk'
      have h11 : f k 1 = 1 := by
        have hk' : ∀ j, j ≤ 4 → f k j = 1 := by
          simpa using hk
        specialize hk' 1 (by omega)
        simpa using hk'
      have h12 : f k 2 = 1 := by
        have hk' : ∀ j, j ≤ 4 → f k j = 1 := by
          simpa using hk
        specialize hk' 2 (by omega)
        simpa using hk'
      have h13 : f k 3 = 1 := by
        have hk' : ∀ j, j ≤ 4 → f k j = 1 := by
          simpa using hk
        specialize hk' 3 (by omega)
        simpa using hk'
      have h14 : f k 4 = 1 := by
        have hk' : ∀ j, j ≤ 4 → f k j = 1 := by
          simpa using hk
        specialize hk' 4 (by omega)
        simpa using hk'
      have h3 : f (k + 1) 0 = f k 1 := by
        specialize h₁ (k + 1) 0 (by linarith) (by rfl)
        simpa using h₁
      have h4 : f (k + 1) 1 = f k (f (k + 1) 0) := by
        specialize h₂ (k + 1) 1 (by linarith) (by simp)
        simpa using h₂
      have h5 : f (k + 1) 2 = f k (f (k + 1) 1) := by
        specialize h₂ (k + 1) 2 (by linarith) (by simp)
        simpa using h₂
      have h6 : f (k + 1) 3 = f k (f (k + 1) 2) := by
        specialize h₂ (k + 1) 3 (by linarith) (by simp)
        simpa using h₂
      have h7 : f (k + 1) 4 = f k (f (k + 1) 3) := by
        specialize h₂ (k + 1) 4 (by linarith) (by simp)
        simpa using h₂
      interval_cases j <;> simp [h3, h4, h5, h6, h7, h10, h11, h12, h13, h14] <;> omega
  have h15 : f 2015 2 = 1 := by 
    have hx := mainthm 2015 (by norm_num) 2 (by norm_num)
    simpa using hx
  exact h15