import Mathlib

theorem number_theory_192332 (S : List ℕ) (hS : S.length = 9)
    (hS1 : ∀ n ∈ S, (Nat.digits 10 n).length = 9)
    (hS2 : ∀ n ∈ S, (Nat.digits 10 n).toFinset.card = 9)
    (hS3 : ∀ n ∈ S, (Nat.digits 10 n).toFinset = Finset.range 10) :
    IsGreatest {k | (List.sum S) % 10^k = 0} 8 := by
  exfalso
  have h1 : S.length = 9 := hS
  have h4 : ∀ n ∈ S, (Nat.digits 10 n).toFinset.card = 9 := hS2
  have h5 : ∀ n ∈ S, (Nat.digits 10 n).toFinset = Finset.range 10 := hS3
  have h6in : S ≠ [] := by
    intro h2
    rw [h2] at hS
    simp at hS
  have h7 : S.head h6in ∈ S := by simp [h6in]
  have h8 := h4 (S.head h6in) (by simp [h6in])
  have h9 := h5 (S.head h6in) (by simp [h6in])
  rw [h9] at h8
  simp [Finset.card_range] at h8
  all_goals omega