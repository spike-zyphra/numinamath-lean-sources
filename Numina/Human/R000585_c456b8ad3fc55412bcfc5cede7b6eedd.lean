import Mathlib

/-Find the only real number that can be expressed in the form \[(a + bi)^3 - 107i,\]where $i^2 = -1,$ and $a$ and $b$ are positive integers.-/
theorem algebra_12920 {x : ℝ}
    (hx : ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ x = (a + Complex.I * b) ^ 3 - 107 * Complex.I)
    : x = 198 := by
  rcases hx with ⟨a, b, _, hb, hx⟩
  have : (a + Complex.I * b) ^ 3 - 107 * Complex.I = (a^3 - 3 * a * b ^ 2) + (3 * a ^ 2 * b - b ^ 3 - 107) * Complex.I := by
    ring_nf
    have : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq, neg_one_mul]
    rw [Complex.I_sq, this]
    ring_nf
  rw [this] at hx

  -- If this is a real number, then we must have 0 = 3a^2b-b^3-107
  have eq : 3 * a ^ 2 * b - b ^ 3 - 107 = (0 : ℝ) := by
    have : 3 * a ^ 2 * b - b ^ 3 - 107 = (x : ℂ).im := by
      rw [hx]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.re_ofNat,
        Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, zero_mul,
        add_zero, Complex.sub_re, Complex.I_im, mul_one, zero_add, Complex.I_re]
      norm_cast
      norm_num
    rw [this]
    norm_cast
  -- or 107 = b(3a^2 - b^2)
  have eq : (107 : ℝ) = b * (3 * a ^ 2 - b ^ 2) := by linarith

  -- this part is to prove Int.subNatNat (3 * a ^ 2) (b ^ 2) = 3 * a ^ 2 - b ^ 2
  have : (0 : ℤ) < 3 * a ^ 2 - b ^ 2 := by
    have : (0 : ℝ) < b * (3 * a ^ 2 - b ^ 2) := by linarith
    rcases (mul_pos_iff.mp this) with ( h1 | h2 )
    . -- 0 < b ∧ 0 < 3 * a ^ 2 - b ^ 2
      norm_cast at h1
      norm_cast
      exact h1.2
    . -- b < 0 ∧ 0 < 3 * a ^ 2 - b ^ 2, but b > 0, so this is a contradiction
      norm_cast at h2
      linarith
  have p: (b ^ 2 : ℤ) < 3 * a ^ 2 := by linarith
  norm_cast at p
  have := Int.ofNat_sub p.le
  norm_cast at this eq
  rw [this.symm] at eq
  norm_cast at eq

  -- Since $107$ is prime, either $b=1$ or $b=107.$
  have : b = 1 ∨ b = 107 := by
    apply (Nat.dvd_prime (by norm_num)).mp
    use (3 * a ^ 2 - b ^ 2)

  -- x = a ^ 3 - 3 * a * b ^ 2
  have hx : (x : ℂ).re = a ^ 3 - 3 * a * b ^ 2 := by
    rw [hx]
    simp
    norm_cast
    norm_num
  simp at hx

  rcases this with (h1 | h2)
  . -- If $b=1,$ then we have $107 = 3a^2-1,$ so $a^2 = 36$ and $a=6.$
    rw [h1] at eq p
    simp at eq p
    have := Int.ofNat_sub p.le
    norm_cast at this
    have : (107 : ℤ) = 3 * a ^ 2 - 1 := by
      norm_cast
      rw [this.symm, eq.symm]
      norm_cast
    have : (a - 6) * (a + 6) = (0 : ℤ) := by linarith
    simp at this
    rcases this with (h3 | h4)
    . -- a = 6
      have h3 : a = 6 := by linarith
      rw [h3, h1] at hx
      field_simp at hx
      linarith
    . -- a = -6, but a > 0, so this is a contradiction
      norm_cast at h4
  . -- If $b = 107,$ then we have $1 = 3a^2 - 107^2,$
    rw [h2] at eq p
    have : 3 * a ^ 2 - 107 ^ 2 = 1 := by linarith
    have : 3 * a^2 - 107 ^ 2 + 107^2 = 107^2 + 1 := by linarith
    rw [Nat.sub_add_cancel p.le] at this

    have eq2 : 107 ^ 2 + 1 ≡ 2 [MOD 3] := by norm_cast
    have eq3 : 3 * a^2 ≡ 0 [MOD 3] := by
      rw [Nat.ModEq]
      simp
    rw [this] at eq3
    absurd eq3
    norm_cast at eq2
