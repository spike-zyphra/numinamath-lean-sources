import Mathlib

theorem algebra_61743 {a b c : ℕ} (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (h : a = b - 2) (h' : b = c - 2) (h'' : ∃ d, d ∈ Finset.Icc 1000 9999 ∧ d % 1111 = 0 ∧
    a^2 + b^2 + c^2 = d) :
    a = 41 ∧ b = 43 ∧ c = 45 := by
  rcases h'' with ⟨d, hd, h1, heq⟩
  rw [Finset.mem_Icc] at hd
  rcases hd with ⟨h4, h5⟩
  have h7 : a = b - 2 := h
  have h8 : b = c - 2 := h'
  have h9 : a = c - 4 := by 
    calc 
      a = b - 2 := h7
      _ = (c - 2) - 2 := by rw [h8]
      _ = c - 4 := by omega
  have h10 : a^2 + b^2 + c^2 = d := by linarith
  rw [show a = c - 4 by linarith [h9], show b = c - 2 by linarith [h8]] at h10
  have h11 : c ≤ 100 := by nlinarith
  interval_cases c <;> omega