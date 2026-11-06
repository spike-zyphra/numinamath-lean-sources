import Mathlib

theorem number_theory_54252 {a b : ℤ} (h : a = a^2 + b^2 - 8 * b - 2 * a * b + 16) :
    IsSquare a := by
  have h1 : a = (a - b) ^ 2 - 8 * b + 16 := by 
    nlinarith
  set k := a - b 
  have h2 : b = a - k := by 
    omega
  have h3 : a = k^2 - 8 * (a - k) + 16 := by
    rw [h2] at h1
    linarith
  have h4 : 9 * a = (k + 4) ^ 2 := by
    nlinarith 
  have h5 : IsSquare (9 * a) := by 
    have h4' : 9 * a = (k + 4) ^ 2 := h4
    use k + 4 
    all_goals 
      nlinarith 
  rcases h5 with ⟨m, hm⟩
  have h6 : 9 * a = m ^ 2 := by 
    nlinarith 
  have h7 : m ^ 2 = 9 * a := by 
    linarith 
  have h9 : m % 3 = 0 := by
    by_contra h10 
    push_neg at h10 
    have h10' : m % 3 = 1 ∨ m % 3 = 2 := by 
      omega 
    have h100 : m ^ 2 % 3 = 1 := by 
      rcases h10' with (h100 | h100)
      · 
        simp [pow_two, Int.mul_emod, h100]
      · 
        simp [pow_two, Int.mul_emod, h100]
    have h11 : 9 * a % 3 = 0 := by 
      omega 
    have h12 : m ^ 2 % 3 = 0 := by 
      omega 
    omega
  have h10 : ∃ n, m = 3 * n := by 
    have h100 : m % 3 = 0 := h9
    have h00 : 3 ∣ m := by 
      omega 
    rcases h00 with ⟨n, hn⟩
    use n 
    all_goals 
      linarith
  rcases h10 with ⟨n, hn⟩
  have h11 : a = n ^ 2 := by 
    rw [hn] at h6 
    nlinarith 
  exact ⟨n, by 
      nlinarith 
  ⟩