import Mathlib

open Nat

theorem number_theory_621269 (hp : ∀ p : ℕ, p.Prime → p - 1 ≡ Nat.factorial (p - 1) [ZMOD p]) :
    Nat.factorial 28 ≡ 15 [ZMOD 31] := by
  have h1 := hp 31 (by norm_num)
  native_decide