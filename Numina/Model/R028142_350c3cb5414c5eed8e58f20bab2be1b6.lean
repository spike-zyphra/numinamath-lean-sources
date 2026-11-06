import Mathlib

theorem number_theory_4478 (B x : ℕ) :
    (Even B → (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + B / 2 * (2 * B)) ∧
    (Odd B → (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + (B - 1) / 2 * (2 * B) + B) := by
  constructor
  · -- Assume B is even.
    intro hB
    have h1 : B % 2 = 0 := by
      obtain ⟨k, hk⟩ := hB
      omega
    have h6 : (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + B / 2 * (2 * B) := by
      have h19 : B % 2 = 0 := h1
      have h20 : ∃ k, B = 2 * k := by
        refine ⟨B / 2, by omega⟩
      rcases h20 with ⟨k, hk⟩
      rw [hk]
      have h8 : (2 * k) / 2 = k := by 
        omega
      rw [h8]
      ring_nf
      <;> omega
    exact h6
  · -- Assume B is odd.
    intro hB
    have h1 : B % 2 = 1 := by
      obtain ⟨k, hk⟩ := hB
      omega
    have h6 : (x * (2 * B) + B) ^ 2 = x * (x + 1) * (2 * B) ^ 2 + (B - 1) / 2 * (2 * B) + B := by
      have h19 : B % 2 = 1 := h1
      have h20 : ∃ k, B = 2 * k + 1 := by
        have h19 : B % 2 = 1 := h1
        have h22 : ∃ k, B = 2 * k + 1 := by
          refine' ⟨(B - 1) / 2, by omega⟩
        exact h22
      rcases h20 with ⟨k, hk⟩
      rw [hk]
      have h8 : (2 * k + 1 - 1) / 2 = k := by 
        omega
      rw [h8]
      ring_nf
      <;> omega
    exact h6