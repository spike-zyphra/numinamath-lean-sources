import Mathlib

/- The number $0.428125$ can be written as a fraction $\frac{a}{b}$ for positive integers $a$ and $b$. When this fraction is in simplest terms, what is $a+b$? -/
theorem number_theory_15152 (a b : ℕ) (ha : a > 0) (hb : b > 0) (h1 : gcd a b = 1) (h2 : (a / b : ℚ) = 0.428125) : a + b = 457 := by
  -- Note on formulation of the problem:
  -- The problem is asking for the fraction in simplest terms, which means that the fraction is irreducible.
  -- For any a, b, such that a > 0, b > 0, gcd a b = 1, a / b = 0.428125, we have a = 137, b = 320.

  -- Rewrite 0.428125 as a fraction, namely 137 / 320
  norm_num at h2
  -- Cancel the denominator at h2
  field_simp at h2
  -- Cast h2 back to ℕ
  norm_cast at h2
  -- We get 320 ∣ 137 * b
  have h : 320 ∣ 137 * b := ⟨a, by omega⟩
  -- Because 320 and 137 are coprime, we have 320 ∣ b
  obtain ⟨c, hc⟩ : 320 ∣ b := Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 320 137 by trivial) h
  -- Substitute b with 320 * c
  subst hc
  -- We get a = 137 * c
  have h3 : a = 137 * c := by
    clear * - h2
    omega
  -- Substitute a with 137 * c
  subst h3
  -- Simplify h1 and we get c = 1
  simp at h1
  rcases h1 with ⟨-, rfl⟩
  simp
