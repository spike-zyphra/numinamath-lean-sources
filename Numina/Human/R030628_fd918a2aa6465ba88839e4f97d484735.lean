import Mathlib

/- Show that the product of two integers of the form $4k + 1$ is again of this form -/
theorem number_theory_4966_1 (a b : ℤ) (ha : ∃ k : ℤ, a = 4 * k + 1) (hb : ∃ k : ℤ, b = 4 * k + 1) :
    ∃ k : ℤ, a * b = 4 * k + 1 := by
  -- the product of two integers of the form $4k + 1$ is again of this form
  -- (4m + 1)(4n + 1) = 4(4mn + m + n) + 1
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use 4 * m * n + m + n
  rw [hm, hn]
  ring

/- while the product of two integers of the form $4k + 3$ is of the form $4k + 1$-/
theorem number_theory_4966_2 (a b : ℤ) (ha : ∃ k : ℤ, a = 4 * k + 3) (hb : ∃ k : ℤ, b = 4 * k + 3) :
    ∃ k : ℤ, a * b = 4 * k + 1 := by
  -- the product of two integers of the form $4k + 3$ is of the form $4k + 1$
  -- (4m + 1)(4n + 1) = 4(4mn + 3m + 3n + 2) + 1
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use 4 * m * n + 3 * m + 3 * n + 2
  rw [hm, hn]
  ring
