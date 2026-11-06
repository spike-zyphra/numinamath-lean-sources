import Mathlib

theorem number_theory_1484 (a : ℕ) (_ : 0 < a) (h : a % 7 = 4) :
    (a^3 + 5) % 7 = 6 := by 
  have h1 : a % 7 = 4 := h
  -- Compute $a^3 \bmod 7$ using the fact that $a \equiv 4 \pmod{7}$:
  -- $a^3 \equiv 4^3 = 64 \equiv 1 \pmod{7}$.
  have h2 : a^3 % 7 = 1 := by
    have h3 : a % 7 = 4 := h1
    norm_num [Nat.pow_mod, h3]
  -- Now to compute $(a^3 + 5) \bmod 7$, we add 5 to $a^3 \bmod 7$ and take modulo 7:
  -- $(a^3 + 5) \bmod 7 = (1 + 5) \bmod 7 = 6 \bmod 7 = 6$
  calc
    (a^3 + 5) % 7 = (a^3 % 7 + 5 % 7) % 7 := by simp [Nat.add_mod]
    _ = (1 + 5) % 7 := by rw [h2]; all_goals norm_num
    _ = 6 % 7 := by norm_num
    _ = 6 := by norm_num