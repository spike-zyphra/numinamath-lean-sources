import Mathlib

theorem algebra_292528 {s : ℂ} (hs : s^7 = 1) (hne : s ≠ 1) :
    s * (s + 1) * (s^2 - s + 1) * (s^2 + s + 1) = -1 := by
  have h1 : s^7 - 1 = 0 := by 
    rw [hs]
    ring_nf
  have h2 : s^7 - 1 = (s - 1) * (s^6 + s^5 + s^4 + s^3 + s^2 + s + 1) := by 
    ring_nf
  rw [h2] at h1
  cases (mul_eq_zero.1 h1) with
  | inl h3 =>
    have hs1 : s = 1 := by
      have : s - 1 = 0 := h3
      have : s = 1 := by
        calc 
          s = (s - 1) + 1 := by ring_nf
          _ = (0) + 1 := by rw [this]; all_goals tauto
          _ = 1 := by ring_nf 
      exact_mod_cast this
    contradiction
  | inr h4 =>
    have h3 : s^6 + s^5 + s^4 + s^3 + s^2 + s + 1 = 0 := by 
      simpa using h4
    have eq1 : (s^2 - s + 1) * (s^2 + s + 1) = s^4 + s^2 + 1 := by
      calc 
        (s^2 - s + 1) * (s^2 + s + 1) 
          = (s^2 + 1 - s) * (s^2 + 1 + s) := by ring_nf 
        _ = (s^2 + 1)^2 - s^2 := by ring_nf 
        _ = s^4 + 2 * s^2 + 1 - s^2 := by ring_nf 
        _ = s^4 + s^2 + 1 := by ring_nf 
    calc 
      s * (s + 1) * (s^2 - s + 1) * (s^2 + s + 1)
          = s * (s + 1) * ((s^2 - s + 1) * (s^2 + s + 1)) := by ring_nf 
      _ = s * (s + 1) * (s^4 + s^2 + 1) := by rw [eq1]
      _ = (s * (s + 1)) * (s^4 + s^2 + 1) := by ring_nf 
      _ = (s^2 + s) * (s^4 + s^2 + 1) := by ring_nf 
      _ = s^2 * (s^4 + s^2 + 1) + s * (s^4 + s^2 + 1) := by ring_nf 
      _ = (s^6 + s^4 + s^2) + (s^5 + s^3 + s) := by ring_nf 
      _ = s^6 + s^5 + s^4 + s^3 + s^2 + s := by ring_nf 
      _ = -1 := by
        have h4' : s^6 + s^5 + s^4 + s^3 + s^2 + s = -1 := by
          have h5 : s^6 + s^5 + s^4 + s^3 + s^2 + s + 1 = 0 := h3
          calc
            s^6 + s^5 + s^4 + s^3 + s^2 + s = (s^6 + s^5 + s^4 + s^3 + s^2 + s + 1) - 1 := by ring_nf 
            _ = 0 - 1 := by rw [h5]
            _ = -1 := by ring_nf 
        exact_mod_cast h4'