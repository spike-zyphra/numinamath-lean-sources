import Mathlib

theorem number_theory_4579 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (habm : a ∣ m ∧ b ∣ m) :
    Nat.lcm a b ∣ m := by 
  rcases habm with ⟨h₁, h₂⟩
  exact Nat.lcm_dvd h₁ h₂