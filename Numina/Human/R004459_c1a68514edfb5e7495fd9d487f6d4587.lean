import Mathlib

/- 137. Diophantine equation. Prove that for any positive integer $a$ the equation $x^{2}-y^{2}=a^{3}$ is solvable in integers. -/
theorem number_theory_269893 (a : ℤ) :
    ∃ x y : ℤ, x ^ 2 - y ^ 2 = a ^ 3 := by
  -- Let x = a * (a + 1) / 2 and y = a * (a - 1) / 2.
  use a * (a + 1) / 2, a * (a - 1) / 2
  qify
  -- It is enough to show that 2 divides n * (n + 1) for any integer n.
  suffices ∀ n : ℤ, 2 ∣ n * (n + 1) by
    push_cast [this, show a * (a - 1) = (a - 1) * (a - 1 + 1) by ring]
    ring
  intro n
  /- An alternative short proof using an existing Mathlib lemma:
  have ⟨m, h⟩ := Int.even_mul_succ_self n
  use m
  linear_combination h
  -/
  -- Rewrite 2 ∣ n * (n + 1) as n * (n + 1) = 0 (mod 2).
  rw [show (2 : ℤ) = (2 : ℕ) by simp, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  generalize (n : ZMod 2) = m
  -- Consider all possible values of n (mod 2) and verify that n * (n + 1) = 0
  -- for n = 0 and n = 1 (mod 2).
  fin_cases m <;> norm_num
  reduce_mod_char