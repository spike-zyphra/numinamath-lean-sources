import Mathlib

theorem number_theory_214935 (n : ℕ) (hn : n > 0) :
    ¬(IsSquare (n + 1) ∧ IsSquare (4 * n + 1)) := by 
  intro h
  rcases h with ⟨h1, h2⟩
  rcases h1 with ⟨a, ha⟩
  rcases h2 with ⟨b, hb⟩
  have eq4 : 4 * a ^ 2 = b ^ 2 + 3 := by 
    have h5 : 4 * n + 1 = b ^ 2 := by 
      nlinarith [hb]
    have h6 : 4 * (n + 1) = 4 * a ^ 2 := by 
      have h7 : n + 1 = a ^ 2 := by 
        linarith [ha]
      rw [h7]
    nlinarith
  have eq5 : b ^ 2 + 3 = 4 * a ^ 2 := by 
    linarith [eq4]
  have eq6 : b % 2 = 1 := by 
    by_contra h
    push_neg at h
    have h8 : b % 2 = 0 := by 
      omega
    have h15 : b ^ 2 % 4 = 0 := by
      have h16 : b % 2 = 0 := h8
      have h17 : b % 4 = 0 ∨ b % 4 = 2 := by 
        omega
      rcases h17 with (h17 | h17)
      · simp [Nat.pow_mod, h17]
      · simp [Nat.pow_mod, h17]
    omega
  have eq8 : ∃ k, b = 2 * k + 1 := by 
    refine' ⟨(b - 1) / 2, by 
      omega 
    ⟩
  rcases eq8 with ⟨k, hk⟩
  have eq9 : 4 * a ^ 2 = 4 * k ^ 2 + 4 * k + 4 := by 
    rw [hk] at eq5
    nlinarith 
  have eq10 : a ^ 2 = k ^ 2 + k + 1 := by 
    nlinarith
  have h11 : k ^ 2 < k ^ 2 + k + 1 := by 
    nlinarith [show (0 : ℕ) ≤ k by omega, show (1 : ℕ) > 0 by norm_num]
  have h12 : k ^ 2 + k + 1 < (k + 1) ^ 2 := by 
    nlinarith [show (0 : ℕ) ≤ k by omega, show (1 : ℕ) > 0 by norm_num]
  have h13 : k < a := by 
    nlinarith [eq10, h11]
  have h14 : a < k + 1 := by 
    nlinarith [eq10, h12]
  omega