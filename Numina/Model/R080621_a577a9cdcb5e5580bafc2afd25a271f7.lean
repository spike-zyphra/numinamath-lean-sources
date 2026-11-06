import Mathlib

theorem algebra_10198 (n : ℤ) :
    (n ^ 2 - 11 * n + 24 ≤ 0 ↔ n ∈ Set.Icc 3 8) := by
  simp only [Set.mem_Icc]
  constructor
  · -- Forward direction: prove if n ^ 2 - 11 * n + 24 ≤ 0 then n ∈ Set.Icc 3 8
    intro h
    constructor
    · -- Show that n ≥ 3
      nlinarith 
    · -- Show that n ≤ 8
      nlinarith 
  · -- Backward direction: prove if n ∈ Set.Icc 3 8 then n ^ 2 - 11 * n + 24 ≤ 0
    rintro ⟨h1, h2⟩
    nlinarith