import Mathlib


open Int


lemma lemma_1 (x : ℤ) : (x + 7) ∣ (x + 11) ↔ (x + 7) ∣ 4 := by
  constructor
  ·
    intro h
    have h1 : (x + 7) ∣ (x + 11) := h
    have h2 : (x + 7) ∣ (x + 11 - (x + 7)) := by
      apply Dvd.dvd.sub
      .
        exact h1
      .
        exact dvd_refl (x + 7)
    have h3 : (x + 11 - (x + 7) : ℤ) = 4 := by
      ring_nf
    rw [h3] at h2
    exact h2
  ·
    intro h
    have h1 : (x + 7) ∣ 4 := h
    have h2 : (x + 7) ∣ (x + 7) := by
      exact dvd_refl (x + 7)
    have h3 : (x + 7) ∣ (x + 11) := by
      have h4 : (x + 7) ∣ ((x + 7) + 4) := by
        apply Dvd.dvd.add
        .
          exact h2
        .
          exact h1
      have h5 : ((x + 7) + 4 : ℤ) = (x + 11) := by
        ring_nf
      rw [h5] at h4
      exact h4
    exact h3


theorem algebra_276665 (x : ℤ) :
    ∃ k : ℤ, (x + 11) / (x + 7) = k ↔ x = -11 ∨ x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3 := by
  by_cases h1 : x = -11 ∨ x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3
  · -- If h1 holds, then (x + 11) / (x + 7) is an integer.
    use (x + 11) / (x + 7)
    simp [h1]
  · -- If h1 does not hold, we need to pick a different k.
    use (x + 11) / (x + 7) + 1
    constructor
    · -- Assume (x + 11) / (x + 7) = k, need to prove x = -11 ∨ x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3.
      intro h
      exfalso
      omega
    · -- Assume x = -11 ∨ x = -9 ∨ x = -8 ∨ x = -6 ∨ x = -5 ∨ x = -3, need to prove (x + 11) / (x + 7) = k.
      intro h
      exfalso
      tauto