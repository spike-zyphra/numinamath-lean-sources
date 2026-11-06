import Mathlib


/--
We consider an ISBN-10 of the form
A₀ 6 2 y 7 0 7 0 1 J₀
with `A₀ = 1`, `J₀ = 2`, and `y : ℕ` satisfying `y < 10`.  We show that the only choice of `y` in `0…9`
that makes the ISBN-10 check equation
10·D₁ + 9·D₂ + 8·D₃ + 7·D₄ + 6·D₅ + 5·D₆ + 4·D₇ + 3·D₈ + 2·D₉ + D₁₀ ≡ 0 (mod 11)
hold is `y = 0`.
-/

theorem isbn_fourth_digit_eq_zero (y : ℕ) (hy : y < 10) :
  let sum := 10*1 + 9*6 + 8*2 + 7*y + 6*7 + 5*0 + 4*7 + 3*0 + 2*1 + 2
  sum % 11 = 0 ↔ y = 0 := by
  -- Expand `sum` and simplify numerically
  let sum := 10*1 + 9*6 + 8*2 + 7*y + 6*7 + 5*0 + 4*7 + 3*0 + 2*1 + 2
  have h_sum : sum = 7*y + 154 := by
    -- compute the constant part: 10 + 54 + 16 + 42 + 28 + 2 + 2 = 154
    simp [sum]; ring
  -- Replace `sum` with `7*y + 154`
  simp only [h_sum]
  -- Now `sum % 11 = (7*y + 154) % 11`.
  -- Observe `154 % 11 = 0`.
  have h154 : 154 % 11 = 0 := by norm_num
  -- Use the fact that 154 % 11 = 0 to simplify
  have calc_result : (7 * y + 154) % 11 = (7 * y) % 11 := by
    rw [Nat.add_mod, h154, add_zero, Nat.mod_mod]
  -- Hence `sum % 11 = 0` iff `(7*y) % 11 = 0`.
  show sum % 11 = 0 ↔ y = 0
  rw [h_sum, calc_result]
  -- `(7*y) % 11 = 0` is equivalent to `11 ∣ 7*y`.
  have mod_dvd : (7 * y) % 11 = 0 ↔ 11 ∣ 7 * y := Nat.dvd_iff_mod_eq_zero.symm
  -- So it suffices to show `11 ∣ 7*y ↔ y = 0` under `y < 10`.
  rw [mod_dvd]
  -- Now show 11 ∣ 7*y ↔ y = 0
  constructor
  · intro h_dvd_7y
    -- Since gcd(7,11) = 1, if 11 ∣ 7*y then 11 ∣ y
    have h_dvd_y : 11 ∣ y := by
      have h11_prime : Nat.Prime 11 := by norm_num
      have h_not_dvd_7 : ¬(11 ∣ 7) := by norm_num
      exact (Nat.Prime.dvd_mul h11_prime).mp h_dvd_7y |>.resolve_left h_not_dvd_7
    -- Since y < 10 < 11, if 11 ∣ y then y = 0
    exact Nat.eq_zero_of_dvd_of_lt h_dvd_y (by linarith [hy])
  · intro h_eq
    rw [h_eq]
    simp