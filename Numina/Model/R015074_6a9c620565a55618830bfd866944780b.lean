import Mathlib

theorem number_theory_197263 (a b c d : ℤ) (h : ∀ x : ℤ, 5 ∣ a*x^3+b*x^2+c*x+d) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h (-1)
  have h4 := h 2
  have h5 := h (-2)
  have h1 : 5 ∣ d := by
    norm_num at h1 ⊢
    omega
  have h2 : 5 ∣ a + b + c + d := by
    norm_num at h2 ⊢
    omega
  have h3 : 5 ∣ -a + b - c + d := by
    norm_num at h3 ⊢
    omega
  have h4 : 5 ∣ 8 * a + 4 * b + 2 * c + d := by
    norm_num at h4 ⊢
    omega
  have h5 : 5 ∣ -8 * a + 4 * b - 2 * c + d := by
    norm_num at h5 ⊢
    omega
  have ha : 5 ∣ a := by 
    omega
  have hb : 5 ∣ b := by
    omega
  have hc : 5 ∣ c := by 
    omega
  have hd : 5 ∣ d := by 
    omega 
  exact ⟨ha, hb, hc, hd⟩