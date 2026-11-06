import Mathlib

theorem number_theory_229924 (a : ℕ → ℕ) (h₀ : ∀ n, 0 ≤ a n ∧ a n ≤ n)
    (h₁ : 451986 = ∑ i in Finset.Icc 1 6, a i * Nat.factorial i) :
    a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 3 ∧ a 4 = 2 ∧ a 5 = 4 ∧ a 6 = 2 := by

  have h21 : 451986 = a 1 * 1 + a 2 * 2 + a 3 * 6 + a 4 * 24 + a 5 * 120 + a 6 * 720 := by
    simp [Finset.sum_Icc_succ_top, Nat.factorial] at h₁
    omega

  have h31 : a 1 ≤ 1 := by 
    have h2 := h₀ 1
    omega

  have h32 : a 1 ≥ 0 := by 
    have h2 := h₀ 1
    omega

  have h33 : a 2 ≤ 2 := by 
    have h2 := h₀ 2
    omega

  have h34 : a 2 ≥ 0 := by 
    have h2 := h₀ 2
    omega

  have h35 : a 3 ≤ 3 := by 
    have h2 := h₀ 3
    omega

  have h36 : a 3 ≥ 0 := by 
    have h2 := h₀ 3
    omega

  have h37 : a 4 ≤ 4 := by 
    have h2 := h₀ 4
    omega

  have h38 : a 4 ≥ 0 := by 
    have h2 := h₀ 4
    omega

  have h39 : a 5 ≤ 5 := by 
    have h2 := h₀ 5
    omega

  have h40 : a 5 ≥ 0 := by 
    have h2 := h₀ 5
    omega

  have h41 : a 6 ≤ 6 := by 
    have h2 := h₀ 6
    omega

  have h42 : a 6 ≥ 0 := by 
    have h2 := h₀ 6
    omega
  
  have h_eq1 : a 1 = 0 := by 
    omega
  
  have h_eq2 : a 2 = 0 := by 
    omega
  
  have h_eq3 : a 3 = 3 := by 
    omega
  
  have h_eq4 : a 4 = 2 := by 
    omega
  
  have h_eq5 : a 5 = 4 := by 
    omega
  
  have h_eq6 : a 6 = 2 := by 
    omega
  
  exact ⟨h_eq1, h_eq2, h_eq3, h_eq4, h_eq5, h_eq6⟩