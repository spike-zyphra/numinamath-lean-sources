import Mathlib

theorem algebra_609983 (squirrels : ℕ → ℝ) (rabbits : ℕ → ℝ) (hs0 : squirrels 0 = 1) (hr0 : rabbits 0 = 1)
    (hsk : ∀ k, squirrels (k + 1) = 2 * squirrels k + 2019) (hrk : ∀ k, rabbits (k + 1) = 4 * rabbits k - 2) :
    IsLeast {k : ℕ | squirrels k < rabbits k} 13 := by
  constructor
  · -- Show that 13 is in the set
    show squirrels 13 < rabbits 13
    norm_num [hs0, hr0, hsk, hrk] at *
  · -- Show that no smaller element is in the set
    intro k hk
    have h3 : squirrels k < rabbits k := by
      simpa using hk
    by_contra h
    push_neg at h
    have h4 : k < 13 := h
    have h5 : k ≤ 12 := by omega
    have h6 : squirrels k ≥ rabbits k := by
      interval_cases k <;> norm_num [hs0, hr0, hsk, hrk] at h3 ⊢ <;> linarith
    linarith