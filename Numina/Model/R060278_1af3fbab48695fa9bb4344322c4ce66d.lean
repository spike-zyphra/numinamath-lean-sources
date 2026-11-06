import Mathlib

theorem number_theory_243147 (a b c d e f : ℕ)
    (h₀ : Even (a + b)) (h₁ : Even (c + d)) (h₂ : Even (e + f))
    (h₃ : 3 ∣ a + c + e) (h₄ : 3 ∣ b + d + f) :
    6 ∣ a + b + c + d + e + f := by 
  have h5 : 2 ∣ a + b + c + d + e + f := by
    have h6 : 2 ∣ a + b := by
      exact Nat.dvd_of_mod_eq_zero (by rw [Nat.even_iff] at h₀; simp [h₀])
    have h7 : 2 ∣ c + d := by 
      exact Nat.dvd_of_mod_eq_zero (by rw [Nat.even_iff] at h₁; simp [h₁])
    have h8 : 2 ∣ e + f := by 
      exact Nat.dvd_of_mod_eq_zero (by rw [Nat.even_iff] at h₂; simp [h₂])
    have h9 : 2 ∣ (a + b) + (c + d) + (e + f) := by 
      omega
    have h10 : a + b + c + d + e + f = (a + b) + (c + d) + (e + f) := by ring
    rw [h10]
    exact h9
  have h4 : 3 ∣ a + b + c + d + e + f := by 
    have h11 : 3 ∣ a + c + e := h₃
    have h12 : 3 ∣ b + d + f := h₄
    have h13 : 3 ∣ (a + c + e) + (b + d + f) := by 
      omega
    have h14 : a + b + c + d + e + f = (a + c + e) + (b + d + f) := by ring
    rw [h14]
    exact h13
  have h_coprime : Nat.Coprime 2 3 := by norm_num
  exact Nat.lcm_dvd h5 h4