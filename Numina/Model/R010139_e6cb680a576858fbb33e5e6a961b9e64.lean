import Mathlib

theorem number_theory_11854 (a : ℕ) (ha : 456 ∣ a) :
    gcd (3 * a ^ 3 + a ^ 2 + 4 * a + 57) a = 57 := by
  -- first prove that the gcd is equal to `gcd (57, a)
  have h2 : gcd (3 * a ^ 3 + a ^ 2 + 4 * a + 57) a = gcd 57 a := by
    -- 3a^3 +a^2+4a+57 = a^2*(3a+1)+4*a+57
    -- So the expression is equal to `57 + a * something`
    have h3 : 3 * a ^ 3 + a ^ 2 + 4 * a + 57 = 57 + a * (a * (3 * a + 1) + 4) := by ring
    rw [h3]
    rw [gcd_eq_nat_gcd, gcd_eq_nat_gcd]
    -- the equality is due to the formula `gcd(a, b) = gcd(a - k*b, b)`
    -- we have `Nat.gcd (57 + a * x) a = Nat.gcd 57 a`.
    simp [Nat.gcd_add_mul_self]
  --  Show that `gcd 57 a = 57`. Since `a` is multiple of 456, so 57 divides a. Then we can get the gcd is 57.
  have h4 : 57 ∣ a := by 
    have h4 : 456 ∣ a := ha
    omega
  rw [h2]
  have h5 : gcd 57 a = 57 := by 
    rw [gcd_eq_nat_gcd]
    -- Assume that 57 divides a, so that `gcd (57, a) =57`.
    simp [Nat.gcd_eq_iff, show 57 ∣ a by omega]
    all_goals omega
  exact h5