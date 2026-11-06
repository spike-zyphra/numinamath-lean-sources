import Mathlib

theorem number_theory_143218 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    11 ∣ n - (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  -- Note: for a 3-digit number n, we have n = 100A + 10B + C, where A, B, C are digits.
  -- We need to prove that n - (100*C + 10*B + A) is divisible by 11.
  -- Let's compute the reversed number: 100*(n % 10) + 10*((n / 10) % 10) + (n / 100)
  -- n - reversed(n) = n - (100*(n % 10) + 10*((n / 10) % 10) + (n / 100))
  -- Let's simplify this algebraically:
  -- Expanding n = 100A + 10B + C
  -- Expanding reversed(n) = 100C + 10B + A
  -- Difference = (100A + 10B + C) - (100C + 10B + A) = 99A - 99C = 99(A - C)
  -- Clearly divisible by 11, as 99 = 9 × 11
  have h3 : n - (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) = 99 * ((n / 100) - (n % 10)) := by 
    omega
  rw [h3]
  -- Now we need to show that 11 divides 99 * ((n / 100) - (n % 10))
  -- But 99 is divisible by 11, so any multiple of 99 is divisible by 11
  omega