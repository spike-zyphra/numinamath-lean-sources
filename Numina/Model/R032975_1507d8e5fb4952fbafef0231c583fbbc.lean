import Mathlib


theorem number_theory_43576 : ¬ (∃ a b c : ℤ, ∀ x : ℤ, 9 ∣ (x + a) * (x + b) * (x + c) - x ^ 3 - 1) := by
  rintro ⟨a, b, c, h⟩
  have eq1 := h 0
  norm_num at eq1
  have eq2 := h 1
  norm_num at eq2
  have eq3 := h (-1)
  norm_num at eq3
  have eq4 := h 2
  norm_num at eq4
  have eq5 := h 3
  norm_num at eq5
  have eq6 := h 4
  norm_num at eq6
  have eq7 := h 5
  norm_num at eq7
  have eq8 := h 6
  norm_num at eq8
  have eq9 := h 7
  norm_num at eq9
  have eq10 := h 8
  norm_num at eq10
  have h1 : (a * b * c : ℤ) % 9 = 1 := by
    omega
  have h2 : (a + b + c) % 9 = 0 := by
    ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 ⊢
    omega
  have h3 : (a * b + b * c + c * a) % 3 = 0 := by
    ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 ⊢
    omega
  have h5 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by 
    omega
  have h6 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by 
    omega
  have h7 : c % 9 = 0 ∨ c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 3 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 6 ∨ c % 9 = 7 ∨ c % 9 = 8 := by 
    omega
  rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;> 
    simp [Int.add_emod, Int.mul_emod, h5, h6, h7, Int.sub_emod, Int.ofNat] at h1 h2 h3 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 ⊢ <;> omega