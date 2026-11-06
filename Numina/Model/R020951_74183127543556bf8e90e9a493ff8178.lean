import Mathlib

theorem number_theory_275154 (M N : Set ℤ)
    (hM : M = {u | ∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l})
    (hN : N = {u | ∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r}) :
    M = N := by
  rw [hM, hN]
  apply Set.ext
  intro u 
  constructor
  · -- First, show that M ⊆ N
    rintro ⟨m, n, l, h⟩
    use m
    use -2 * m + 2 * n + l
    use 2 * m - 2 * n - l
    linarith 
  · -- Now show that N ⊆ M
    rintro ⟨p, q, r, h⟩
    use p
    use p + 2 * q + r
    use r 
    linarith