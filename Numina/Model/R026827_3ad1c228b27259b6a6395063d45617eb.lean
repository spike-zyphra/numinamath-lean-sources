import Mathlib

theorem number_theory_202805 (a m : ℤ) :
    ∀ x, x ≡ a [ZMOD m] ↔ ∃ t, x = m * t + a := by
  intro x
  constructor
  · -- Assume x ≡ a [ZMOD m], prove ∃ t, x = m * t + a
    rintro (h : x ≡ a [ZMOD m])
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
    refine' ⟨-t, by linarith⟩
  · -- Assume ∃ t, x = m * t + a, prove x ≡ a [ZMOD m]
    rintro ⟨t, ht⟩
    have h : x - a = m * t := by linarith
    exact Int.modEq_iff_dvd.mpr ⟨-t, by linarith⟩