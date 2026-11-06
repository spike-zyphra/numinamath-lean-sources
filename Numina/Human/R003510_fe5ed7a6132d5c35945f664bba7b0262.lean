import Mathlib

/-$a$ and $b$ are positive integers. When written in binary, $a$ has 2004 1 's,
and $b$ has 20051 's (not necessarily consecutive).
What is the smallest number of 1's $a+b$ could possibly have?-/
theorem number_theory_189526 :
  IsLeast {k | ∃(a b : ℕ), a > 0 ∧ b > 0 ∧
  (Nat.digits 2 a).sum = 2004 ∧
  (Nat.digits 2 b).sum = 2005 ∧
  (Nat.digits 2 (a + b)).sum = k} 1 := by
  constructor
  · -- Show that 1 is achievable
    use 2^4008 - 2^2005 + 1, 2^2005 - 1
    native_decide
  · -- Show that 1 is the smallest value
    intro k hk
    rcases hk with ⟨a, b, ha_pos, hb_pos, ha1s, hb1s, hab1s⟩
    have hm : a + b ≠ 0 := by omega
    -- The binary digits of a + b form a non-empty list
    have h1:(Nat.digits 2 (a + b))≠[]:=by
      exact Nat.digits_ne_nil_iff_ne_zero.mpr hm
    -- The last digit (most significant bit) is non-zero
    have h2:(Nat.digits 2 (a + b)).getLast h1 ≠ 0:=by
      exact Nat.getLast_digit_ne_zero 2 hm
    let r:=(Nat.digits 2 (a + b)).getLast h1
    have r0:r=(Nat.digits 2 (a + b)).getLast h1 := by rfl
    rw[←r0] at h2
    -- The sum of digits is at least the last digit, which is at least 1
    have h3:(Nat.digits 2 (a + b)).sum≥ r:=by
      apply List.le_sum_of_mem
      exact List.getLast_mem h1
    omega
