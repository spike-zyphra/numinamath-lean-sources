import Mathlib.Tactic

theorem number_theory_150630 (r : ℤ) (_ : r > 0) :
    ∃ m n, m^2 - n^2 = r^3 :=
by
  use (r^2 + r) / 2, (r^2 - r) / 2
  -- Now we need to show that m^2 - n^2 = r^3
  -- where m = (r^2 + r)/2 and n = (r^2 - r)/2.
  have eq1 : ((r^2 + r) / 2 : ℤ) ^ 2 - ((r^2 - r) / 2 : ℤ) ^ 2 = r^3 := by
    have eq2 : ((r^2 + r) / 2 : ℤ) ^ 2 - ((r^2 - r) / 2 : ℤ) ^ 2 =
        (((r^2 + r) / 2 : ℤ) + ((r^2 - r) / 2 : ℤ)) * (((r^2 + r) / 2 : ℤ) - ((r^2 - r) / 2 : ℤ)) := by
      ring
    have eq3 : ((r^2 + r) / 2 : ℤ) + ((r^2 - r) / 2 : ℤ) = r^2 := by
      have eq4 : (r : ℤ) % 2 = 0 ∨ (r : ℤ) % 2 = 1 := by omega
      cases eq4 with 
      | inl h0 =>
        have h7 : (r : ℤ) % 2 = 0 := h0
        have h8 : ∃ k, r = 2 * k := by
          refine' ⟨r / 2, by omega⟩
        rcases h8 with ⟨k, hk⟩
        rw [hk]
        ring_nf
        <;> omega
      | inr h1 =>
        have h7 : (r : ℤ) % 2 = 1 := h1
        have h9 : ∃ k, r = 2 * k + 1 := by
          have h8 : r % 2 = 1 := h7
          have h12 : r = 2 * (r / 2) + 1 := by
            omega
          refine' ⟨r / 2, by
            omega⟩
        rcases h9 with ⟨k, hk⟩
        rw [hk]
        ring_nf
        <;> omega
      all_goals omega
    have eq5 : ((r^2 + r) / 2 : ℤ) - ((r^2 - r) / 2 : ℤ) = r := by
      have eq6 : (r : ℤ) % 2 = 0 ∨ (r : ℤ) % 2 = 1 := by omega
      cases eq6 with 
      | inl h0 =>
        have h7 : (r : ℤ) % 2 = 0 := h0
        have h8 : ∃ k, r = 2 * k := by
          refine' ⟨r / 2, by omega⟩
        rcases h8 with ⟨k, hk⟩
        rw [hk]
        ring_nf
        <;> omega
      | inr h1 =>
        have h7 : (r : ℤ) % 2 = 1 := h1
        have h9 : ∃ k, r = 2 * k + 1 := by
          have h8 : r % 2 = 1 := h7
          have h12 : r = 2 * (r / 2) + 1 := by
            omega
          refine' ⟨r / 2, by
            omega⟩
        rcases h9 with ⟨k, hk⟩
        rw [hk]
        ring_nf
        <;> omega
      all_goals omega
    rw [eq2, eq3, eq5]
    all_goals ring_nf <;> omega
  linarith [eq1]
  all_goals linarith