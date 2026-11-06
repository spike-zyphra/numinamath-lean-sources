import Mathlib

/- $a$, $b$, $c$, $d$ are distinct positive integers, and $abcd=441$, then the value of $a+b+c+d$ is ( )

A:$30$
B:$32$
C:$34$
D:$36$   -/
theorem number_theory_626126 (a b c d : ℕ)
    (hpos : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0)
    (hdist : [a, b, c, d].Nodup)
    (hprod : a * b * c * d = 441) :
    a + b + c + d = 32 := by
  -- `hpos` is redundant since it is implied by `hprod`.
  clear hpos
  -- We show that `a`, `b`, `c`, `d` are all divisors of `441`.
  have ha : a ∈ Nat.divisors 441 := by
    simp
    exact ⟨b * c * d, by linear_combination -hprod⟩
  have hb : b ∈ Nat.divisors 441 := by
    simp
    exact ⟨a * c * d, by linear_combination -hprod⟩
  have hc : c ∈ Nat.divisors 441 := by
    simp
    exact ⟨a * b * d, by linear_combination -hprod⟩
  have hd : d ∈ Nat.divisors 441 := by
    simp
    exact ⟨a * b * c, by linear_combination -hprod⟩
  -- We calculate the divisors of `441`.
  have h441 : Nat.divisors 441 = {1, 3, 7, 9, 21, 49, 63, 147, 441} := by native_decide
  rw [h441] at ha hb hc hd
  -- Now we revert the assumptions and variables.
  revert hprod hdist
  revert d
  revert c
  revert b
  revert a
  -- Now the goal reads `∀ a ∈ {1, 3, 7, 9, 21, 49, 63, 147, 441},
  -- ∀ b ∈ {1, 3, 7, 9, 21, 49, 63, 147, 441},
  --   ∀ c ∈ {1, 3, 7, 9, 21, 49, 63, 147, 441},
  --    ∀ d ∈ {1, 3, 7, 9, 21, 49, 63, 147, 441}, [a, b, c, d].Nodup → a * b * c * d = 441 → a + b + c + d = 32`
  -- It is computably decidable.
  native_decide
