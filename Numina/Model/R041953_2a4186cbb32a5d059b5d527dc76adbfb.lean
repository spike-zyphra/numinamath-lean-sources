import Mathlib

theorem number_theory_163473 (a b c d e : ℤ) (h₀ : a + b + c + d + e = 0) :
    15 ∣ a^5 + b^5 + c^5 + d^5 + e^5 := by
  have base_mod3 : ∀ (x : ℤ), x ^ 5 % 3 = x % 3 := by
    intro x
    have h1 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
      omega
    rcases h1 with (h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h1 : a ^ 5 % 3 = a % 3 := base_mod3 a
  have h2 : b ^ 5 % 3 = b % 3 := base_mod3 b
  have h3 : c ^ 5 % 3 = c % 3 := base_mod3 c
  have h4 : d ^ 5 % 3 = d % 3 := base_mod3 d
  have h5 : e ^ 5 % 3 = e % 3 := base_mod3 e
  have base_mod5 : ∀ (x : ℤ), x ^ 5 % 5 = x % 5 := by
    intro x
    have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h7 : a ^ 5 % 5 = a % 5 := base_mod5 a
  have h8 : b ^ 5 % 5 = b % 5 := base_mod5 b
  have h9 : c ^ 5 % 5 = c % 5 := base_mod5 c
  have h10 : d ^ 5 % 5 = d % 5 := base_mod5 d
  have h11 : e ^ 5 % 5 = e % 5 := base_mod5 e
  have h6 : (a^5 + b^5 + c^5 + d^5 + e^5) % 3 = 0 := by
    omega
  have h12 : (a^5 + b^5 + c^5 + d^5 + e^5) % 5 = 0 := by
    omega
  omega