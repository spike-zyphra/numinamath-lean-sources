import Mathlib

def t (n : ℕ) := n * (n + 1) / 2

theorem number_theory_324711 :
    IsLeast {k | 0 < k ∧ Function.Periodic (fun n => t n % 10) k} 20 := by 
  constructor 
  · -- Show 20 is in the set
    constructor
    · norm_num -- 0 < 20
    · -- Show the function is periodic with period 20
      unfold Function.Periodic
      intro n 
      have h1 : t (n + 20) % 10 = t n % 10 := by 
        simp [t] 
        have h2 : (n + 20) * (n + 21) = n * (n + 1) + 40 * n + 420 := by 
          ring_nf 
        have h7 : (n + 20) * (n + 21) / 2 % 10 = n * (n + 1) / 2 % 10 := by
          have h8 : n % 20 = 0 ∨ n % 20 = 1 ∨ n % 20 = 2 ∨ n % 20 = 3 ∨ n % 20 = 4 ∨ n % 20 = 5 ∨ n % 20 = 6 ∨ n % 20 = 7 ∨ n % 20 = 8 ∨ n % 20 = 9 ∨ n % 20 = 10 ∨ n % 20 = 11 ∨ n % 20 = 12 ∨ n % 20 = 13 ∨ n % 20 = 14 ∨ n % 20 = 15 ∨ n % 20 = 16 ∨ n % 20 = 17 ∨ n % 20 = 18 ∨ n % 20 = 19 := by omega
          rcases h8 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.add_mod, Nat.mul_mod, Nat.add_comm] at *
          <;> omega 
        exact_mod_cast h7 
      exact_mod_cast h1 
  · -- Show 20 is the least 
    intro k hk 
    rcases hk with ⟨hk_pos, h_k⟩ 
    by_contra h 
    push_neg at h 
    have h1 : ∀ n : ℕ, t (n + k) % 10 = t n % 10 := by 
      intro n 
      have h2 := h_k 
      simpa using h2 n 
    have hk0 := h1 0 
    simp [t] at hk0 
    have hk1 := h1 1 
    simp [t] at hk1 
    have hk2 := h1 2 
    simp [t] at hk2 
    have hk3 := h1 3 
    simp [t] at hk3 
    have hk4 := h1 4 
    simp [t] at hk4 
    have hk5 := h1 5 
    simp [t] at hk5 
    have hk6 := h1 6 
    simp [t] at hk6 
    have hk7 := h1 7 
    simp [t] at hk7 
    have hk8 := h1 8 
    simp [t] at hk8 
    have hk9 := h1 9 
    simp [t] at hk9 
    have hk10 := h1 10 
    simp [t] at hk10 
    have hk11 := h1 11 
    simp [t] at hk11 
    have hk12 := h1 12 
    simp [t] at hk12 
    have hk13 := h1 13 
    simp [t] at hk13 
    have hk14 := h1 14 
    simp [t] at hk14 
    have hk15 := h1 15 
    simp [t] at hk15 
    have hk16 := h1 16 
    simp [t] at hk16 
    have hk17 := h1 17 
    simp [t] at hk17 
    have hk18 := h1 18 
    simp [t] at hk18 
    have hk19 := h1 19 
    simp [t] at hk19 
    interval_cases k <;> omega 
    all_goals omega