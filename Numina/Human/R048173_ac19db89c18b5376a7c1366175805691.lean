import Mathlib

open Int

/-
Show that if \( a \) is an odd integer, then \( a^{2} \equiv 1 \mod 8 \).
-/
theorem number_theory_4652 (a : ℤ) (h₀ : Odd a) : a^2 ≡ 1 [ZMOD 8] := by
  dsimp [Int.ModEq]
  -- Given $a$ is odd, we can write it as $2k + 1$ for some integer $k$.
  rcases h₀ with ⟨k, hk⟩
  rw [hk]
  -- Thus we have $(2k + 1)^2 \% 8 = 1$
  ring_nf
  -- Next, we consider the cases where $k$ is even or odd.
  cases (Int.even_or_odd k) with
  | inl h =>
    -- If $k$ is even, then $k = 2r$ for some integer $r$.
    rcases h with ⟨r, hr⟩
    rw [hr]; ring_nf
    -- That is to say $(1 + r*8 + r^2*16) \% 8 = 1$
    rw [(show r^2 * 16 = (r^2 * 2) * 8 by ring_nf),Int.add_mul_emod_self,Int.add_mul_emod_self]
    -- which as equal to $1 \% 8 = 1$, this is trivial.
    rfl
  | inr h =>
    -- If $k$ is odd, then $k = 2r + 1$ for some integer $r$.
    rcases h with ⟨r, hr⟩
    -- Thus we have $(1 + 1 * 8 + r * 3 * 8 + r ^ 2 * 2 * 8) \% 8 = 1$
    rw [hr]; ring_nf
    rw [(show 9 + r * 24 + r^2 * 16 = 1 + 1 * 8 + r * 3 * 8 + r^2 * 2 * 8 by ring_nf)]
    repeat rw [Int.add_mul_emod_self]
    -- Which can be reduced to $1 \% 8 = 1$, this is also trivial.
    rfl
