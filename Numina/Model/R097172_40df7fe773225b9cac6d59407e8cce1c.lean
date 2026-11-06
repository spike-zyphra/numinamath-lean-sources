import Mathlib

theorem number_theory_219861 : IsGreatest {x | 0 < x ∧ (19^x : ℕ) ∣ Nat.factorial 2017} 111 := by 
  constructor
  · -- Show 111 is indeed in the set
    constructor
    · -- Show 111 > 0
      norm_num
    · -- Show that (19^111) divides Nat.factorial 2017
      native_decide
  · -- Show that if x is in the set, then x ≤ 111
    intro x hx
    rcases hx with ⟨hx_pos, hx_div⟩
    have h1 : x ≤ 111 := by
      by_contra h 
      push_neg at h 
      have h2 : x ≥ 112 := by omega 
      have h3 : (19 ^ 112 : ℕ) ∣ (19 ^ x : ℕ) := by 
        exact pow_dvd_pow _ (by omega) 
      have h4 : (19 ^ 112 : ℕ) ∣ Nat.factorial 2017 := by 
        exact dvd_trans h3 hx_div 
      have h5 : ¬((19 ^ 112 : ℕ) ∣ Nat.factorial 2017) := by 
        native_decide 
      exact h5 h4 
    linarith