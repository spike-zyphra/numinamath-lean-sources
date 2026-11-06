import Mathlib

theorem number_theory_257007 (x : ℤ) :
    (∃ t1, x = 105 * t1 + 52) ↔
    ∃ t2 t3 t4, x - 3 = 7 * t2 ∧ x - 2 = 5 * t3 ∧ x - 4 = 3 * t4 := by
  constructor
  · -- Assume ∃ t1, x = 105 * t1 + 52, prove ∃ t2 t3 t4, ...
    rintro ⟨t1, hx⟩
    refine ⟨15 * t1 + 7, 21 * t1 + 10, 35 * t1 + 16, ?_, ?_, ?_⟩
    · -- Show x - 3 = 7 * t2
      rw [hx]
      omega
    · -- Show x - 2 = 5 * t3
      rw [hx]
      omega
    · -- Show x - 4 = 3 * t4
      rw [hx]
      omega
  · -- Assume ∃ t2 t3 t4, ..., prove ∃ t1, x = 105 * t1 + 52
    rintro ⟨t2, t3, t4, h1, h2, h3⟩
    have h4 : x % 7 = 3 := by
      omega
    -- x ≡ 2 (mod 5)
    have h5 : x % 5 = 2 := by
      omega
    -- x ≡ 4 (mod 3), which is equivalent to x ≡ 1 (mod 3)
    have h6 : x % 3 = 1 := by
      omega
    -- From these congruences, we can solve for x.
    -- As earlier steps shows, the solution is x = 105t1 + 52.
    use (x - 52) / 105
    omega