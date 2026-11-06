import Mathlib

/- A particular number written in base 3 requires three digits (${\_ \_ \_}_3$). When the number is written in base 3 and 4, the digits are the reverse of each other. What is this number expressed in base 10? -/
theorem number_theory_19596 {a b c n : ℕ}
  (h₁: Nat.digits 3 n = [c,b,a]) (h₂: Nat.digits 4 n = [a,b,c])
  (h₃: a ≠ 0):
  n = 22 := by
  -- suppose the number n is abc_(base 3), then n = ax3^2+bx3+c. and since a need 3 digits, the first digit(a) cannot be zero. or else it only need 2 or less digits.
  have h1: n = 9*a+3*b+c := by
    rw [← Nat.ofDigits_digits 3 n, h₁]
    rw [Nat.ofDigits, Nat.ofDigits]; simp; ring
  -- when it's written in base 4, digits are reversed, i.e., it is cba. then n = cx4^2+bx4+a
  have h2: n = 16*c+4*b+a := by
    rw [← Nat.ofDigits_digits 4 n, h₂]
    rw [Nat.ofDigits, Nat.ofDigits]; simp; ring
  -- so 9a+3b+c = 16c+4b+a, or 8a = 15c+b
  have h3: 8*a = 15*c+b := by
    have hh1: 9*a+3*b+c = 16*c+4*b+a := by
      rw [← h1, ← h2]
    have hh2: 9*a+3*b+c = 8*a + (a+3*b+c) := by ring
    have hh3: 16*c+4*b+a = 15*c+b + (a+3*b+c) := by ring
    rw [hh2, hh3] at hh1
    apply Nat.add_right_cancel hh1
  -- notice that abc are digits from base 3, so they can only be 0,1,2
  have ha: a < 3 := by
    have: a ∈ Nat.digits 3 n := by
      rw [h₁]; simp
    exact Nat.digits_lt_base' this
  have hb: b < 3 := by
    have: b ∈ Nat.digits 3 n := by
      rw [h₁]; simp
    exact Nat.digits_lt_base' this
  have apos: 0 < a := Nat.zero_lt_of_ne_zero h₃
  -- so we just try them, and see if any number satisfy.
  interval_cases a <;> simp at * <;> simp [*]
  · -- when a=1, 8=15c+b, no such c and b.
    interval_cases b <;> simp at * <;> omega
  · -- when a=2, 16=15c+b.
    interval_cases b
    · simp at h3; omega
    · --we solve c=1,b=1. then n = 9a+3b+c=18+3+1=22.
      simp at h3; rw [h3]; norm_num
    · simp at h3; omega