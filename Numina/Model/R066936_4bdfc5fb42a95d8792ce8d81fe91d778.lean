import Mathlib

theorem number_theory_275388 {a b : ℤ} (h : Odd (a + b)) : Even (a * b) := by 
  have h1 : a % 2 = 0 ∨ b % 2 = 0 := by
    have h_odd : (a + b) % 2 = 1 := by
      obtain ⟨k, hk⟩ := h
      have : (a + b) % 2 = 1 := by
        rw [hk]
        omega
      exact this
    -- Now that we have (a + b) % 2 = 1, we need to show either a or b is 0 mod 2
    -- This is equivalent to (a % 2 + b % 2) % 2 = 1 
    have eq1 : (a + b) % 2 = (a % 2 + b % 2) % 2 := by 
      omega
    rw [eq1] at h_odd
    -- Now we need to show that either a % 2 = 0 or b % 2 = 0 by contradiction
    omega
  cases h1 with
  | inl h1 =>
    -- Assume a % 2 = 0, then a is even, so there exists k such that a = 2k
    have h2 : a % 2 = 0 := h1
    have h3 : ∃ k, a = 2 * k := by 
      refine' ⟨a / 2, ?_⟩
      omega
    rcases h3 with ⟨k, hk⟩
    -- Then a * b = (2k) * b = 2 * (k * b)
    -- So a * b is even
    use k * b
    rw [hk]
    ring_nf
  | inr h1 =>
    -- Assume b % 2 = 0, then b is even, so there exists k such that b = 2k
    have h2 : b % 2 = 0 := h1
    have h3 : ∃ k, b = 2 * k := by 
      refine' ⟨b / 2, ?_⟩
      omega
    rcases h3 with ⟨k, hk⟩
    -- Then a * b = a * (2k) = 2 * (a * k)
    -- So a * b is even
    use a * k
    rw [hk]
    ring_nf