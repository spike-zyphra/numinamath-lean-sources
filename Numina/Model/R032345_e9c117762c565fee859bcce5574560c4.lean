import Mathlib

theorem number_theory_160748 (p : ℕ) (hp : Nat.Prime p) :
    ¬ IsSquare (p^3 + p + 1) := by 
  by_contra h
  rcases h with ⟨k, hk⟩
  have h1 : k^2 = p^3 + p + 1 := by
    nlinarith 
  -- The key idea is to consider the equation modulo 4.
  -- If $k^2 = p^3 + p + 1$, then $k^2 \pmod{4}$ must be either 0 or 1.
  -- Let's analyze $p^3 + p + 1 \pmod{4}$ for primes $p$.
  have h3 : p ≥ 2 := Nat.Prime.two_le hp
  by_cases h4 : p % 2 = 0
  · -- p is even, so p=2
    have h5 : p = 2 := by
      by_cases h6 : p > 2
      · -- p > 2, even
        have h7 : ¬Nat.Prime p := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        tauto
      · -- p <= 2, prime
        interval_cases p <;> trivial
    rw [h5] at h1
    have h8 : k ≤ 3 := by nlinarith
    interval_cases k <;> omega
  · -- p is odd
    have h4' : p % 2 = 1 := by 
      omega
    -- Now analyzing the equation modulo 4.
    -- If $p$ is odd, then $p \equiv 1$ or $3 \pmod{4}$.
    -- Computing $p^3 + p + 1$ in both cases:
    -- Case 1: p ≡1 (mod 4): 1^3+1+1=3 (mod 4)
    -- Case 2: p ≡3 (mod 4): 3^3+3+1=31≡3 (mod 4)
    -- Therefore k^2 ≡3 (mod 4), which is invalid.
    have h8 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by 
      have h11 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by 
        omega
      rcases h11 with (h | h | h | h) <;> 
        simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    have h9 : (p ^ 3 + p + 1) % 4 = 3 := by
      by_cases h10 : p % 4 = 1
      · 
        have : p % 4 = 1 := h10
        have h11 : p % 4 = 1 := this
        have h12 : p ^ 3 % 4 = 1 := by 
          have : p % 4 = 1 := h11
          have : p % 4 = 1 := this
          simp [Nat.pow_mod, this]
        omega
      · 
        have : p % 4 = 3 := by
          omega
        have h11 : p % 4 = 3 := this
        have h12 : p ^ 3 % 4 = 3 := by 
          have : p % 4 = 3 := h11
          have : p % 4 = 3 := this
          simp [Nat.pow_mod, this]
        omega
    have h10 : k ^ 2 % 4 = 3 := by
      omega
    omega