import Mathlib

theorem number_theory_198126 (m n : ℤ) : 16 ∣ (5 * m + 3 * n + 1)^5 * (3 * m + n + 4)^4 := by

  have h1 : (m + n) % 2 = 0 ∨ (m + n) % 2 = 1 := by
    omega

  rcases h1 with (h | h)
  · -- case where m +n is even
    have h2 : (3 * m + n + 4) % 2 = 0 := by
      have h3 : (m + n) % 2 = 0 := h
      omega

    have h2' : ∃ k : ℤ, 3 * m + n + 4 = 2 * k := by 
      refine' ⟨(3 * m + n + 4) / 2, by omega⟩

    rcases h2' with ⟨k, hk⟩
    use ( (5 * m + 3 * n + 1)^5 * k^4 )
    rw [show (3 * m + n + 4) = 2 * k by linarith]
    ring_nf

  · -- case where m +n is odd
    have h2 : (5 * m + 3 * n + 1) % 2 = 0 := by 
      omega

    have h2' : ∃ k : ℤ, 5 * m + 3 * n + 1 = 2 * k := by 
      refine' ⟨(5 * m + 3 * n + 1) / 2, by omega⟩

    rcases h2' with ⟨k, hk⟩

    use ( k^5 * (3 * m + n + 4)^4 * 2 )

    rw [show 5 * m + 3 * n + 1 = 2 * k by linarith]
    ring_nf