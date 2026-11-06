import Mathlib

/- gcd(a,ak+b) = gcd(a,b) -/
lemma gcd_add_mul (a b : ℤ) : a.gcd (a * k + b) = a.gcd b := by
  by_cases ha : a = 0
  · simp [ha]
  · suffices
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + b * y} =
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + (a * k + b) * y}
    from IsLeast.unique
      (this ▸ Int.gcd_least_linear ha (b := a * k + b))
      (Int.gcd_least_linear ha (b := b))
    ext n
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    refine fun _ => ⟨fun ⟨x, y, h⟩ => ?_, fun ⟨x, y, h⟩ => ?_⟩
    · use x - k * y, y; simp [h]; ring
    · use x + k * y, y; simp [h]; ring

/- Let \( m \) and \( n \) be positive integers and let \( a \) be an integer greater than one.
  Show that the greatest common divisor of \( a^m - 1 \) and \( a^n - 1 \) is equal to \( a^{\gcd(m, n)} - 1 \). -/
theorem number_theory_4540 {m n : ℕ} {a : ℤ} (ha : a > 1) :
    gcd (a ^ m - 1) (a ^ n - 1) = a ^ gcd m n - 1 := by
  -- use Nat.gcd.induction
  apply Nat.gcd.induction (P := fun m n => gcd (a ^ m - 1) (a ^ n - 1) = a ^ gcd m n - 1)
  -- check base case : gcd(a^0-1, a^n-1) = a^gcd(0, n)-1
  · intro n
    simp only [pow_zero, sub_self, gcd_zero_left, normalize_eq]
    refine (Int.nonneg_iff_normalize_eq_self (a ^ n - 1)).mpr ?_
    norm_num
    exact one_le_pow₀ (le_of_lt ha)
  · clear m n
    rintro m n - eq
    -- rewrite gcd(n%m, m) to gcd(m,n) at hypothesis
    conv_rhs at eq => rw [gcd_eq_nat_gcd, ← Nat.gcd_rec, ← gcd_eq_nat_gcd]
    -- use hypothesis
    rw [← eq, gcd_comm]
    clear eq
    obtain ⟨k, hk⟩ : a ^ m - 1 ∣ a ^ n - a ^ (n % m) :=
      Int.dvd_trans
        (pow_one_sub_dvd_pow_mul_sub_one a m (n / m))
        ⟨a ^ (n % m), by simp [sub_mul, ← pow_add, Nat.div_add_mod]⟩
    -- use lemma to draw a conclusion
    rw [show a ^ n - 1 = (a ^ m - 1) * k + (a ^ (n % m) - 1) by rw [← hk]; ring,
      gcd_comm, ← Int.coe_gcd, gcd_add_mul, Int.coe_gcd, gcd_comm]
