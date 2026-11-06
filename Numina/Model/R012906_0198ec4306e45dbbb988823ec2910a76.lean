import Mathlib

theorem number_theory_114295 (n : ℕ) :
    ¬ ∃ m, m^2 = ∑ i ∈ Finset.range 10, (n + i)^2 := by
  rintro ⟨m, hm⟩
  norm_num [Finset.sum_range_succ] at hm
  have h1 : m^2 = 10 * n^2 + 90 * n + 285 := by
    nlinarith [hm]
  -- Now, we show this leads to a contradiction modulo 5.
  -- From h1, m^2 = 5 * (2 * n^2 + 18 * n + 57).
  have h2 : m^2 = 5 * (2 * n^2 + 18 * n + 57) := by
    nlinarith
  -- From m^2 = 5 * ..., we know m^2 is divisible by 5, which implies m must be divisible by 5.
  have h3 : m ^ 2 % 5 = 0 := by
    omega
  -- From m^2 % 5 = 0, we must have m % 5 = 0
  have h4 : m % 5 = 0 := by 
    have h5 : m ^ 2 % 5 = 0 := h3
    have h6 : m % 5 = 0 := by 
      have : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
        omega
      rcases this with (h | h | h | h | h) <;> 
        simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at h5 <;> try { 
          omega 
        }
    assumption
  -- Therefore, m is a multiple of 5. Let m = 5k
  have h7 : ∃ k, m = 5 * k := by 
    refine' ⟨m / 5, by omega⟩
  rcases h7 with ⟨k, hk⟩
  -- Substitute m = 5k into h1. Then $m^2 = 25k^2 = 10n^2 + 90n + 285$
  rw [show m = 5 * k by linarith [hk]] at h1
  -- Simplify to obtain $5k^2 = 2n^2 + 18n + 57$
  have h8 : 5 * k^2 = 2 * n^2 + 18 * n + 57 := by
    nlinarith
  -- From $5k^2 = 2n^2+18n+57$, we have $2n^2+18n+57$ must be divisible by 5.
  -- We check this congruence modulo 5. $2n^2+18n+57 \equiv 2n^2+3n+2 \pmod{5}$.
  -- We show none of the residues satisfy $2n^2+3n+2 \equiv 0 \pmod{5}$.
  have h9 : (2 * n^2 + 18 * n + 57) % 5 = 0 := by 
    omega
  -- However this is impossible.
  have h10 : (n) % 5 = 0 ∨ (n) % 5 = 1 ∨ (n) % 5 = 2 ∨ (n) % 5 = 3 ∨ (n) % 5 = 4 := by
    omega
  rcases h10 with (h | h | h | h | h) <;> 
    simp [h, Nat.pow_mod, Nat.add_mod, Nat.mul_mod] at h9
    <;> try { 
      all_goals omega 
    }
    <;> try { 
      all_goals nlinarith 
    }