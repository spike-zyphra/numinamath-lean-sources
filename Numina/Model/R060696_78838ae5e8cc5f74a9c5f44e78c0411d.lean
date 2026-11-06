import Mathlib

theorem number_theory_122993 (a : ℤ) :
    ∃ k : ℤ, 2 * a^2 = 7 * k + 2 ↔ ∃ ℓ : ℤ, a = 7 * ℓ + 1 ∨ a = 7 * ℓ - 1 := by
  use (2 * a^2 - 2) / 7
  constructor
  · -- Forward direction: if 2a^2 = 7k + 2 for some integer k, then a = 7ℓ ± 1 for some integer ℓ
    intro h
    have h1 : a^2 % 7 = 1 % 7 := by
      -- Show a^2 ≡ 1 (mod 7)
      have h1 : (2 * a^2) % 7 = 2 % 7 := by
        omega
      -- Multiply both sides of a congruence by the inverse of 2 modulo 7
      omega
    -- We have a^2 ≡ 1 (mod 7), so either a ≡ 1 (mod 7) or a ≡ 6 (mod 7)
    have : a % 7 = 1 ∨ a % 7 = 6 := by
      have h1 : a^2 % 7 = 1 % 7 := by
        omega
      have h2 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by 
        omega
      rcases h2 with (h | h | h | h | h | h | h) <;> 
        ( 
          norm_num [h, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at h1 
          <;> 
          try { 
            omega 
          }
        )
    -- Now convert the modular conditions into the desired form
    rcases this with (h | h)
    · -- Case a ≡ 1 (mod 7)
      use (a - 1) / 7
      left
      omega
    · -- Case a ≡ 6 (mod 7)
      use (a + 1) / 7
      right
      omega
  · -- Backward direction: if a = 7ℓ ± 1 for some integer ℓ, then 2a^2 = 7k + 2 for some integer k
    rintro ⟨ℓ, h⟩
    rcases h with (h | h)
    · -- Case a = 7ℓ + 1
      have h1 : a = 7 * ℓ + 1 := h
      rw [h1]
      -- Compute 2 * (7ℓ + 1)^2 - 2 and show it's divisible by 7
      ring_nf
      <;> omega
    · -- Case a = 7ℓ - 1
      have h2 : a = 7 * ℓ - 1 := h
      rw [h2]
      -- Compute 2 * (7ℓ - 1)^2 - 2 and show it's divisible by 7
      ring_nf
      <;> omega