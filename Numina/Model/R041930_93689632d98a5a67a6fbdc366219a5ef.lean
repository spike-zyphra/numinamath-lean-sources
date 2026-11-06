import Mathlib

theorem number_theory_192658 (f s : ℕ → ℕ)
    (hs : ∀ n, s n = (Nat.digits 10 n).sum)
    (h₀ : ∀ n, 0 < n → (n < 10 → f n = 0) ∧ (n ≥ 10 → f n = f (s n) + 1)) :
    ¬∀ n m, 0 < n → n < m → f n ≤ f m := by

  intro h
  have h1 := h 99 100 (by norm_num) (by norm_num)
  have h2 : f 99 = 2 := by
    have h3 := (h₀ 99 (by norm_num)).2 (by norm_num)
    have h4 : s 99 = 18 := by 
      rw [hs 99]
      norm_num
    have h5 := (h₀ 18 (by norm_num)).2 (by norm_num)
    have h6 : s 18 = 9 := by 
      rw [hs 18]
      norm_num
    have h7 := (h₀ 9 (by norm_num)).1 (by norm_num)
    simp [h6, h7] at h5 
    simp [h4, h5] at h3 
    linarith
  have h3 : f 100 = 1 := by
    have h4 := (h₀ 100 (by norm_num)).2 (by norm_num)
    have h5 : s 100 = 1 := by 
      rw [hs 100]
      norm_num
    have h6 := (h₀ 1 (by norm_num)).1 (by norm_num)
    simp [h5, h6] at h4
    linarith
  linarith [h1, h2, h3]