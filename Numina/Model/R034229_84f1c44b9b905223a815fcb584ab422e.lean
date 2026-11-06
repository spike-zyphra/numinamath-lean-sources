import Mathlib

theorem number_theory_245887 (f : ℕ → ℕ)
    (h₀ : ∀ n m, f (n * m) = f n + f m)
    (h₁ : ∀ n, Nat.Prime n → n > 10 → f n = 0)
    (h₂ : f 1 < f 243 ∧ f 243 < f 2 ∧ f 2 < 11)
    (h₃ : f 2106 < 11) :
    f 96 = 31 := by

  have h4 : f 1 = 0 := by 
    have h7 : f (1 * 1) = f 1 + f 1 := h₀ 1 1 
    simp at h7 
    omega

  have h5 : f 1 < f 243 := h₂.1 
  have h6 : f 243 < f 2 := h₂.2.1 
  have h7 : f 2 < 11 := h₂.2.2

  have h8 : f 243 = 5 * f 3 := by
    calc
      f 243 = f (3 * 81) := by norm_num
      _ = f 3 + f 81 := by rw [h₀ 3 81]
      _ = f 3 + f (3 * 27) := by norm_num 
      _ = f 3 + (f 3 + f 27) := by rw [h₀ 3 27]
      _ = f 3 + (f 3 + f (3 * 9) ) := by norm_num 
      _ = f 3 + (f 3 + (f 3 + f 9) ) := by rw [h₀ 3 9]
      _ = f 3 + (f 3 + (f 3 + f (3 * 3) ) ) := by norm_num 
      _ = f 3 + (f 3 + (f 3 + (f 3 + f 3) ) ) := by rw [h₀ 3 3]
      _ = 5 * f 3 := by omega 

  have h9 : f 2106 = f 2 + 4 * f 3 := by
    calc
      f 2106 = f (2 * 1053) := by norm_num 
      _ = f 2 + f 1053 := by rw [h₀ 2 1053]
      _ = f 2 + f (3 * 351) := by norm_num 
      _ = f 2 + (f 3 + f 351) := by rw [h₀ 3 351]
      _ = f 2 + (f 3 + f (3 * 117) ) := by norm_num 
      _ = f 2 + (f 3 + (f 3 + f 117) ) := by rw [h₀ 3 117]
      _ = f 2 + (f 3 + (f 3 + f (3 * 39) ) ) := by norm_num 
      _ = f 2 + (f 3 + (f 3 + (f 3 + f 39) ) ) := by rw [h₀ 3 39]
      _ = f 2 + (f 3 + (f 3 + (f 3 + f (3 * 13) ) ) ) := by norm_num 
      _ = f 2 + (f 3 + (f 3 + (f 3 + (f 3 + f 13) ) ) ) := by rw [h₀ 3 13]
      _ = f 2 + (f 3 + (f 3 + (f 3 + (f 3 + 0) ) ) ) := by 
        have h13 : f 13 = 0 := by
          apply h₁ 13 
          norm_num 
          all_goals norm_num 
        simp [h13]
      _ = f 2 + 4 * f 3 := by omega

  have h3p : f 3 = 1 := by
    have h42 : f 1 < f 243 := h₂.1
    rw [h4] at h42
    rw [h8] at h42
    have h43 : f 243 < f 2 := h₂.2.1
    rw [h8] at h43
    have h44 : f 2 < 11 := h₂.2.2
    omega

  have h2p : f 2 = 6 := by
    have h42 : f 1 < f 243 := h₂.1
    rw [h4] at h42
    rw [h8] at h42
    have h43 : f 243 < f 2 := h₂.2.1
    rw [h8] at h43
    have h44 : f 2 < 11 := h₂.2.2
    omega

  have h96' : f 96 = 5 * f 2 + f 3 := by
    calc
      f 96 = f (2 * 48) := by norm_num
      _ = f 2 + f 48 := by rw [h₀ 2 48]
      _ = f 2 + f (2 * 24) := by norm_num
      _ = f 2 + (f 2 + f 24) := by rw [h₀ 2 24]
      _ = f 2 + (f 2 + f (2 * 12) ) := by norm_num
      _ = f 2 + (f 2 + (f 2 + f 12) ) := by rw [h₀ 2 12]
      _ = f 2 + (f 2 + (f 2 + f (2 * 6) ) ) := by norm_num
      _ = f 2 + (f 2 + (f 2 + (f 2 + f 6) ) ) := by rw [h₀ 2 6]
      _ = f 2 + (f 2 + (f 2 + (f 2 + f (2 * 3) ) ) ) := by norm_num
      _ = f 2 + (f 2 + (f 2 + (f 2 + (f 2 + f 3) ) ) ) := by rw [h₀ 2 3]
      _ = 5 * f 2 + f 3 := by omega

  rw [h96']
  omega