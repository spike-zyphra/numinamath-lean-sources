import Mathlib

theorem number_theory_275492 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : ¬ 37 ∣ n) (h₃ : ¬ 37 ∣ m) (h₄ : 37 ∣ n + m) :
    37 ∣ (n * 1000 + m) := by 
  have h5 : n ≥ 100 := Finset.mem_Icc.mp h₀ |>.1
  have h6 : n ≤ 999 := Finset.mem_Icc.mp h₀ |>.2
  have h7 : m ≥ 100 := Finset.mem_Icc.mp h₁ |>.1
  have h8 : m ≤ 999 := Finset.mem_Icc.mp h₁ |>.2
  
  have h9 : n * 1000 + m = n * 999 + (n + m) := by 
    omega
  
  rw [h9]
  
  have h10 : 37 ∣ n * 999 := by 
    omega
  
  have h11 : 37 ∣ (n * 999 + (n + m)) := by 
    apply Nat.dvd_add h10 h₄
  
  exact h11