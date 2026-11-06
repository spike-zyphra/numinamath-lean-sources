import Mathlib

theorem number_theory_571 {n : ℕ} (h : n ∈ Finset.Icc 10000 99999) (h2 : 823 ∣ n) (h3 : Nat.digits 10 n = [3, 4, 7, 3, 3]) : n = 33743 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h4, h5⟩
  have h6 : n = 33743 := by 
    have h7 : n = Nat.ofDigits 10 (Nat.digits 10 n) := by 
      rw [Nat.ofDigits_digits]
      all_goals omega 
    rw [h3] at h7
    rw [h7]
    all_goals native_decide 
  exact h6