import Mathlib

theorem number_theory_244428 (S : Finset ℕ) (hS : ∀ x ∈ S, x > 0)
    (hS1 : ∀ a b : ℕ, a ∈ S → b ∈ S → Nat.gcd a b > 1)
    (hS2 : ∀ a b c : ℕ, a ∈ S → b ∈ S → c ∈ S → Nat.gcd (Nat.gcd a b) c = 1) :
    S.card ≠ 2012 := by
  have h2 : ∀ a : ℕ, a ∈ S → False := by 
    intro a ha
    have h11 : Nat.gcd a a > 1 := hS1 a a (by simp [ha]) (by simp [ha])
    have h13 : Nat.gcd (Nat.gcd a a) a = 1 := hS2 a a a (by simp [ha]) (by simp [ha]) (by simp [ha])
    have h14 : a = 1 := by 
      rw [show Nat.gcd a a = a by 
        simp [Nat.gcd_self]
      ] at h13 
      simp [Nat.gcd_comm] at h13 
      all_goals omega 
    rw [show Nat.gcd a a = a by 
        simp [Nat.gcd_self]
    ] at h11 
    omega 
  have h1 : S.card = 0 := by
    have h3 : S = (∅ : Finset ℕ) := by 
      apply Finset.eq_empty_iff_forall_not_mem.mpr 
      intro a ha
      have h4 : a ∈ S := by simpa using ha 
      specialize h2 a h4 
      tauto 
    rw [h3]
    simp 
  have h3 : S.card ≠ 2012 := by 
    rw [h1]
    all_goals norm_num 
  exact h3