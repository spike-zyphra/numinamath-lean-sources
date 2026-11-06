import Mathlib

/- Find all positive integers  $a$  and  $b$  such that  $ ab+1 \mid a^2-1$  -/
theorem number_theory_8686 {a b : ℤ} (hapos : 0 < a) (hbpos : 0 < b) :
    a * b + 1 ∣ a ^ 2 - 1 ↔ a = 1 ∨ b = 1 := by
  constructor
  swap
  -- Verify that a=1 and b=1 are solutions.
  . rintro (rfl | rfl)
    . simp
    . simp [show a ^ 2 - 1 = (a + 1) * (a - 1) by ring]
  intro hab
  -- We have ab+1 | a^2b + a.
  have h1 := Int.dvd_mul_left a (a * b + 1)
  -- We have ab+1 | a^2b - a
  have h2 := Dvd.dvd.mul_left hab b
  -- Combining above we have ab+1 | a + b
  have := Dvd.dvd.sub h1 h2
  ring_nf at this
  -- Hence we have ab+1 ≤ a + b.
  have := Int.le_of_dvd (by linarith) this
  rcases le_or_lt a b with h | h
  -- If a ≤ b, we can deduce that a = 1.
  . have : a*b < 2*b := by linarith
    have : a < 2 := by nlinarith
    have : a = 1 := by omega
    exact Or.inl this
  -- Otherwise, we can deduce b=1.
  have : a*b < 2*a := by linarith
  have : b < 2 := by nlinarith
  have : b = 1 := by omega
  exact Or.inr this
