import Mathlib

theorem number_theory_197192 : ¬ ∃ p q : ℤ, ∀ x : ℤ, 3 ∣ x^2 + p * x + q := by
  intro h
  rcases h with ⟨p, q, h⟩
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  have h4 : q % 3 = 0 := by 
    omega
  have h5 : (1 + p + q) % 3 = 0 := by 
    omega
  have h6 : (4 + 2 * p + q) % 3 = 0 := by 
    omega
  -- Now we have three congruences:
  -- 1. q ≡ 0 (mod 3).
  -- 2. (1 + p + q) ≡ 0 (mod 3).
  -- 3. (4 + 2p + q) ≡ 0 (mod 3).
  -- Using these congruences, we will show a contradiction.
  omega