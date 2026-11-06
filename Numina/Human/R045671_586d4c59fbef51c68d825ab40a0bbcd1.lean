import Mathlib

/- 5. Find all pairs of positive integers $(a, b)$ such that

$$

a b+2=a^{3}+2 b .

$$
 -/
theorem algebra_146608 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b + 2 = a^3 + 2 * b) :
    (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 25) ∨ (a = 4 ∧ b = 31) ∨
    (a = 5 ∧ b = 41) ∨ (a = 8 ∧ b = 85) := by
  -- It is more convenient to work with integers.
  -- Replace (a : ℕ) with (x : ℤ) = a and (b : ℕ) with (y : ℤ) = b.
  zify at *
  set x := (a : ℤ)
  set y := (b : ℤ)
  -- x * y + 2 = x ^ 3 + 2 * y implies that (x - 2) * y = (x - 2) * (x ^ 2 + 2 * x + 4) + 6.
  have hx : (x - 2) * y = (x - 2) * (x ^ 2 + 2 * x + 4) + 6 := by
    linear_combination h
  -- Show that x - 2 divides 6.
  replace hx : x - 2 ∣ 6 := by
    -- We have that x - 2 divides (x - 2) * (x ^ 2 + 2 * x + 4) + 6 so x - 2 must divide 6.
    rw [← Int.dvd_add_right (b := (x - 2) * (x ^ 2 + 2 * x + 4))]
    · use b
      rw [hx]
    · use x ^ 2 + 2 * x + 4
  -- Consider all possible integer divisors of 6 and find out that x = 1, x = 3, x = 4, x = 5, or x = 8.
  replace hx : x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 8 := by
    have h : (x - 2).natAbs ∈ (6).divisors := by
      have ⟨k, hk⟩ := hx
      simp; use k.natAbs; rw [←Int.natAbs_mul, ← hk]; rfl
    simp [show (6 : ℕ).divisors = {1, 2, 3, 6} from rfl] at h
    omega
  -- Find corresponding values of y for each value of x.
  rcases hx with hx | hx | hx | hx | hx <;> rw [hx] at h <;> omega