import Mathlib

theorem number_theory_4637
(m a b : ℤ):
a ≡ b [ZMOD m] ↔ ∃ k, a = b + k * m := by
  constructor
  · -- Assume a ≡ b [ZMOD m], need to show ∃ k, a = b + k * m
    intro h
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
    use -k
    linarith
  · -- Assume ∃ k, a = b + k * m, need to show a ≡ b [ZMOD m]
    rintro ⟨k, hk⟩
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linarith⟩