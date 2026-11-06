import Mathlib

theorem number_theory_103412 {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h1 : m % 7 = 1) (h2 : m % 8 = 4) (h3 : m % 9 = 7)
    (h4 : n % 8 = 5) (h5 : n % 9 = 7) :
    72 ∣ (m + 20) ∧ 72 ∣ (n + 11) := by 
  have h10 : (m + 20) % 8 = 0 := by 
    omega
  have h11 : (m + 20) % 9 = 0 := by 
    omega
  have h14 : 72 ∣ (m + 20) := by 
    omega
  have h12 : (n + 11) % 8 = 0 := by 
    omega
  have h13 : (n + 11) % 9 = 0 := by 
    omega
  have h15 : 72 ∣ (n + 11) := by 
    omega
  exact ⟨h14, h15⟩