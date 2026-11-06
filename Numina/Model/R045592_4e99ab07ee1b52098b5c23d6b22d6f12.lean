import Mathlib

theorem number_theory_4736 (a b c : ℤ) (hc : c ≠ 0) : a ∣ b ↔ a * c ∣ b * c := by 
  constructor
  · -- Assume a divides b, we need to show a * c divides b * c
    intro h 
    obtain ⟨k, hk⟩ := h
    use k 
    rw [show b * c = a * c * k by
      calc
        b * c = (a * k) * c := by rw [show b = a * k by linarith]
        _ = a * c * k := by ring
    ]
  · -- Assume a * c divides b * c, we need to show a divides b
    intro h 
    rcases h with ⟨m, hm⟩ 
    have h_eq : b * c = a * c * m := by 
      linarith 
    have h_eq2 : b * c = (a * m) * c := by 
      ring_nf at h_eq ⊢ 
      linarith 
    have h_eq3 : b = a * m := by
      apply (mul_right_inj' hc).mp
      linarith
    exact ⟨m, by linarith⟩