import Mathlib

/-- The number nn can be written in base 1414 as abc,
    can be written in base 15 as acb,
    and can be written in base 6 as acac​, where a>0.
    Find the base-10 representation of n. -/
theorem number_theory_97476 {n : ℕ} (hn : n > 0) (h1 : Nat.digits 14 n = [c, b, a])
    (h2 : Nat.digits 15 n = [b, c, a]) (h3 : Nat.digits 6 n = [c, a, c, a]) :
    n = 925 := by
  -- The assumptions translate to c + 14(b + 14a) = n,
  have h14 := Nat.ofDigits_digits 14 n
  rw[h1] at h14
  -- b + 15(c + 14a) = n,
  have h15 := Nat.ofDigits_digits 15 n
  rw[h2] at h15
  -- c + 6(a + 6(c + 6a)) = n.
  have h6 := Nat.ofDigits_digits 6 n
  rw[h3] at h6
  simp[Nat.ofDigits_cons] at h14 h15 h6
  rw[← h14] at h15
  -- Combining the latter two gets us 3a + b = 22c.
  have eq1 : 3 * a + b = 22 * c := by linarith
  -- a must be between 1 and 5:
  obtain ⟨nea,lta⟩ : 0 < a ∧ a < 6 := by
    -- Since it is a leading digit, it is positive.
    have := Nat.getLast_digit_ne_zero 14 hn.ne'
    constructor
    · linarith
    -- Since it is a digit mod 6, it is < 6.
    · have : a ∈ Nat.digits 6 n := by rw[h3]; simp
      exact Nat.digits_lt_base (by simp) this
  -- Hence, c is not 0.
  have nec : c ≠ 0 := by
    rintro rfl
    omega
  -- Also, b must be less than 14, since it is a digit mod 14.
  have ltb : b < 14 := by
    have : b ∈ Nat.digits 14 n := by rw[h1]; simp
    exact Nat.digits_lt_base (by simp) this    
  have le1 : 1 ≤ a := nea.succ_le
  -- By testing all possible values for a, we see that c = 1.
  obtain rfl : c = 1 := by interval_cases a <;> omega
  rw[← h6] at h14
  -- From this we get b = 22-3a
  obtain rfl : b = 22 - 3 * a := by omega
  -- and a = 4, b = 10, c = 1, n = 925.
  obtain rfl : a = 4 := by linarith
  exact h6.symm