import Mathlib

theorem number_theory_223955 {x : ℕ} (hx : x > 0) (h : ∃ r, Even r ∧ r ≥ 18 ∧
    (Nat.digits r (x ^ 2)).length = 8 ∧ (Nat.digits r (x ^ 2)).headI ≠ 0 ∧
    (Nat.digits r (x ^ 2)).tail.reverse = (Nat.digits r (x ^ 2)) ∧
    (Nat.digits r (x ^ 2))[3]! - (Nat.digits r (x ^ 2))[2]! = 2) :
    r = 24 := by
  rcases h with ⟨r, hr1, hr2, h1, h2, h2', h3⟩
  have h7 : (Nat.digits r (x ^ 2)).length = 8 := h1
  have h8 : (Nat.digits r (x ^ 2)).tail.reverse = (Nat.digits r (x ^ 2)) := h2'
  have h9 : (Nat.digits r (x ^ 2)).length = 8 := h1
  have h10 : ((Nat.digits r (x ^ 2)).tail).length = 7 := by
    rw [List.length_tail]
    all_goals
      omega
  have h11 : ((Nat.digits r (x ^ 2)).tail.reverse).length = 7 := by
    rw [List.length_reverse]
    all_goals
      omega
  have h12 : (Nat.digits r (x ^ 2)).length = 8 := h1
  have h13 : (Nat.digits r (x ^ 2)).tail.reverse = (Nat.digits r (x ^ 2)) := h2'
  have h14 : ((Nat.digits r (x ^ 2)).tail.reverse).length = (Nat.digits r (x ^ 2)).length := by
    rw [h13]
  rw [h11] at h14
  rw [h12] at h14
  all_goals omega