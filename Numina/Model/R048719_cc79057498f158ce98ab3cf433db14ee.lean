import Mathlib

theorem number_theory_19550 (a : ℕ) (ha : a > 0) :
    Nat.digits a 55 = [1, 3, 1] ↔ a = 6 := by
  constructor
  · -- Forward: if Nat.digits a 55 = [1,3,1], then a = 6
    intro h_eq
    have h1 : a ≤ 55 := by
      by_contra h
      push_neg at h
      have h2 : Nat.digits a 55 = [55] := by
        simp [h]
      rw [h2] at h_eq
      norm_num at h_eq
      all_goals linarith
    interval_cases a <;> norm_num at h_eq ⊢ <;> try { simp_all }
    <;> norm_num at h_eq <;> try { contradiction }
  · -- Reverse: if a = 6, then Nat.digits a 55 = [1,3,1]
    intro h_eq
    rw [h_eq]
    norm_num