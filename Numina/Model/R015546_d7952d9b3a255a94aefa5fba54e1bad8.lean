import Mathlib

theorem algebra_170401 {b c d : ℤ} (ha : ∀ n, ∃ m, Odd m ∧ m = n + c ∧ b * ⌊Real.sqrt (m + c)⌋ + d = 5) :
    b + c + d = 2 := by 
  have h1 := ha 0 
  rcases h1 with ⟨m0, h_odd0, h_eq0, h_eq5_0⟩ 
  have h_eq0' : m0 = c := by linarith 
  have h_c_odd : (c : ℤ) % 2 = 1 := by 
    have h1_odd : (m0 : ℤ) % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h_odd0 
      omega 
    rw [h_eq0'] at h1_odd 
    omega 
  have h2 := ha 1 
  rcases h2 with ⟨m1, h_odd1, h_eq1, h_eq5_1⟩ 
  have h_eq1' : m1 = 1 + c := by linarith 
  have h_c_even : (c : ℤ) % 2 = 0 := by 
    have h1_odd : (m1 : ℤ) % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h_odd1 
      omega 
    rw [h_eq1'] at h1_odd 
    omega 
  omega 
  all_goals try { contradiction }
  <;> nlinarith