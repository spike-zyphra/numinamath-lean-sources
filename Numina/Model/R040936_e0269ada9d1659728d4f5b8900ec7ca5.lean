import Mathlib

theorem number_theory_256591 :
    IsGreatest {m | (Nat.factorial m) ∣ Nat.factorial 100 + Nat.factorial 99 + Nat.factorial 98} 98 := by 
  constructor 
  · -- Show that 98! divides $100! + 99! + 98!$.
    native_decide
  · intro m hm
    have h : (Nat.factorial m) ∣ (Nat.factorial 100 + Nat.factorial 99 + Nat.factorial 98) := hm
    by_contra h1 
    push_neg at h1 
    have h2 : m ≥ 99 := by omega
    have h3 : (Nat.factorial 99) ∣ (Nat.factorial m) := by 
      apply Nat.factorial_dvd_factorial 
      omega 
    have h4 : (Nat.factorial 99) ∣ (Nat.factorial 100 + Nat.factorial 99 + Nat.factorial 98) := by 
      have h5 : (Nat.factorial m) ∣ (Nat.factorial 100 + Nat.factorial 99 + Nat.factorial 98) := h 
      have h6 : (Nat.factorial 99) ∣ (Nat.factorial m) := h3 
      exact dvd_trans h6 h5 
    have h5 : ¬ (Nat.factorial 99 ∣ (Nat.factorial 100 + Nat.factorial 99 + Nat.factorial 98)) := by
      native_decide 
    exfalso 
    exact h5 h4