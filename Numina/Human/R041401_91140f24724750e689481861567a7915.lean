import Mathlib

/-Find all prime numbers $p$ and $q$ for which $p^{2} - 2 q^{2}=1$.-/
theorem number_theory_197142 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    p^2 - 2 * q^2 = 1 ↔ (p = 3 ∧ q = 2) := by
  constructor
  · -- Forward direction: if p^2 - 2 * q^2 = 1 then (p = 3 ∧ q = 2)
    intro h
    have h1 : q = 2 := by
      by_cases hq2 : q = 2
      · exact hq2
      · -- If q ≠ 2, then q is an odd prime ≥ 3
        have hq_odd : Odd q := Nat.Prime.odd_of_ne_two hq (by omega)
        have hq_ge_3 : q ≥ 3 := by
          by_contra h'
          push_neg at h'
          have : q ≤ 2 := by linarith
          interval_cases q <;> norm_num at *
        have h_mod : q % 2 = 1 := Nat.odd_iff.mp hq_odd
        have hq2 : q ^ 2 % 4 = 1 := by
          have h1 : q % 2 = 1 := h_mod
          have h2 : q % 4 = 1 ∨ q % 4 = 3 := by
            omega
          rcases h2 with (h2 | h2)
          · -- q % 4 = 1
            have h3 : q ^ 2 % 4 = 1 := by
              norm_num [Nat.pow_mod, h2]
            exact h3
          · -- q % 4 = 3
            have h3 : q ^ 2 % 4 = 1 := by
              norm_num [Nat.pow_mod, h2]
            exact h3
        have h2 : (2 * q ^ 2) % 4 = 2 := by
          omega
        have h3 : p ^ 2 % 4 = 3 := by
          omega
        have h4 : p ^ 2 % 4 = 0 ∨ p ^ 2 % 4 = 1 := by
          have h2 : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by
            omega
          rcases h2 with (h2 | h2 | h2 | h2) <;> (
            norm_num [Nat.pow_mod, h2] at *
          )
        omega
    have h2 : p = 3 := by
      rw [h1] at h
      have h3 : p ^ 2 = 9 := by
        omega
      have h4 : p = 3 := by
        have h4 : p ≤ 3 := by nlinarith
        interval_cases p <;> tauto
      exact h4
    exact ⟨h2, h1⟩
  · -- Reverse direction: (p = 3 ∧ q = 2) → p^2 - 2 * q^2 = 1
    rintro ⟨rfl, rfl⟩
    norm_num