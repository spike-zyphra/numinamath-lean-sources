import Mathlib

theorem number_theory_49590 {f : ℕ → ℂ} (hf : ∀ m n, f m * f n = f (m * n))
    (h : ∀ m, f m ≠ 0) (N : ℕ → ℕ) (hN : StrictMono N)
    (hN' : ∀ k, ∃ A, A ≠ 0 ∧ ∀ n, N k ≤ n ∧ n ≤ N k + 4 * Real.sqrt (N k) → f n = A) :
    ∀ n, f n = 1 := by
  have h1 : f 0 = 1 := by 
    have h50 : f 0 ≠ 0 := h 0 
    have h6 : f 0 * f 0 = f 0 := by 
      specialize hf 0 0 
      norm_num at hf 
      all_goals tauto 
    have h7 : f 0 - 1 = 0 := by 
      have hne0 : f 0 ≠ 0 := h50 
      have eq1 : f 0 * (f 0 - 1) = 0 := by 
        calc 
          f 0 * (f 0 - 1) = f 0 * f 0 - f 0 := by ring 
          _ = f 0 - f 0 := by rw [h6]
          _ = (0 : ℂ) := by ring 
      cases' (mul_eq_zero.mp eq1) with h4 h4 
      · 
        exfalso 
        exact hne0 (by simpa using h4)
      · 
        exact_mod_cast h4
    have h8 : f 0 = 1 := by
      exact_mod_cast sub_eq_zero.mp h7 
    exact_mod_cast h8
  intro N 
  have eq1 : f (N) * f 0 = f (N * 0) := hf N 0 
  rw [show N * 0 = (0:ℕ) by omega] at eq1 
  rw [h1] at eq1 
  have h3 : f N ≠ 0 := h N 
  have eq2 : f N = (1 : ℂ) := by
    have eq3 : f N * (1 : ℂ) = (1 : ℂ) := eq1
    have h_eq : f N = (1 : ℂ) := by 
      simp [Complex.ext_iff] at eq3 ⊢
      all_goals 
        try tauto
    exact_mod_cast h_eq 
  exact_mod_cast eq2