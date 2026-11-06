import Mathlib

theorem number_theory_14814 (b : ℕ) (hb : b > 1) :
    (Nat.digits b 100).length = 5 ↔ b = 3 := by
  constructor
  · -- First direction: if the length of the digits is 5, then b = 3
    intro h
    have h1 : b ≤ 100 := by
      by_contra h2
      push_neg at h2
      have h3 : (Nat.digits b 100).length = 1 := by
        simp [h2]
      omega
    interval_cases b <;> norm_num at h ⊢ <;> try { all_goals try { tauto } }
  · -- Second direction: if b = 3, then the length of the digits is 5
    intro h
    rw [h]
    norm_num