import Mathlib

/- Let S be the set of all positive rational numbers r such that when the two numbers r and 55r are written as fractions in lowest terms, the sum of the numerator and denominator of one fraction is the same as the sum of the numerator and denominator of the other fraction. The sum of all the elements of S can be expressed in the form p / q, where p and q are relatively prime positive integers. Find p + q. -/
theorem number_theory_98662 {S : Set ℚ} (hS : S = {r | r > 0 ∧ (r.num + (r.den : ℤ)) = (55 * r).num + (55 * r).den}) :
    ∀ p q : ℕ, p > 0 ∧ q > 0 ∧ p.Coprime q ∧ ∑ᶠ r ∈ S, r = p / q → p + q = 719 := by
  -- we will show that S contains two rational numbers: 2 / 25 and 5 / 22
  suffices S = {2 / 25, 5 / 22} by
    rw [this, finsum_mem_eq_toFinset_sum]
    intro p q ⟨hp, pq, hpq, heq⟩
    norm_num at heq
    field_simp at heq
    suffices p = 169 ∧ q = 550 by omega
    zify
    apply Rat.div_int_inj <;> norm_cast
    apply (NNRat.divNat_inj _ _).mpr <;> try omega
    qify
    linarith
  rw [hS]
  symm; ext r; simp; constructor
  -- it is easy to show that 2 / 25 ∈ S and 5 / 22 ∈ S
  · intro h; cases' h with h h <;> rw [h] <;> norm_num
  -- we have 0 < r and r.num + r.den = (55 * r).num + (55 * r).den
  intro ⟨hr, heq⟩
  -- let a = r.num.natAbs ∈ ℕ and b = r.den ∈ ℕ
  set a := r.num.natAbs with ha
  set b := r.den with hb
  -- 0 < r implies that r.num > 0 and hence r.num = r.num.natAbs = a
  have har : r.num = a := by
    rw [ha, Int.natAbs_of_nonneg]
    rw [Rat.num_nonneg]
    exact le_of_lt hr
  have hreq : r = a / b := by
    rw [←Rat.num_div_den r, har, hb]
    norm_num
  -- we have (55 * r).num = 55 * r.num / gcd (55 * r.num) r.den
  -- and (55 * r).den = r.den / gcd (55 * r.num) r.den
  rw [Rat.mul_num, Rat.mul_den, ←hb, har] at heq
  norm_cast at heq
  simp at heq
  -- gcd (55 * a) b = gcd 55 b (since a and b are coprime)
  -- all possible values of gcd 55 b are all divisors of 55: 1, 5, 11, or 55
  have hgcd : (55 * a).gcd b ∈ ({1, 5, 11, 55} : Finset ℕ) := by
    have hab : a.Coprime b := r.reduced
    rw [Nat.Coprime.gcd_mul_right_cancel _ hab]
    have : Nat.gcd 55 b ∈ (55).divisors := by
      simp
      exact Nat.gcd_dvd_left 55 b
    rw [show (55 : ℕ).divisors = {1, 5, 11, 55} by rfl] at this
    exact this
  simp at hgcd
  -- consider all possible values of gcd (55 * a) b
  rcases hgcd with hgcd | hgcd | hgcd | hgcd <;> simp [hgcd] at heq
  -- if gcd = 1 then we get a = 55 * a which is impossible (since 0 < a)
  · suffices 0 < a by omega
    apply Nat.zero_lt_of_ne_zero
    rw [ha, ne_eq, Int.natAbs_eq_zero, Rat.num_eq_zero]
    exact ne_of_gt hr
  -- if gcd = 5 then b = 5 * k and we get a + 5 * k = 11 * a + k
  -- it is easy to derive that 10 * a = 4 * k, 5 * a = 2 * k
  -- hence, 25 * a = 2 * b and a / b = 2 / 25
  · have ⟨k, hk⟩ : 5 ∣ b := by rw [←hgcd]; apply Nat.gcd_dvd_right
    rw [hreq]
    field_simp
    norm_cast
    left; omega
  -- if gcd = 11 then b = 11 * k and we get a + 11 * k = 5 * a + k
  -- it is easy to derive that 4 * a = 10 * k, 2 * a = 5 * k
  -- hence, 22 * a = 5 * b and a / b = 5 / 22
  · have ⟨k, hk⟩ : 11 ∣ b := by rw [←hgcd]; apply Nat.gcd_dvd_right
    rw [hreq]
    field_simp
    norm_cast
    right; omega
  -- if gcd = 55 then b = b / 55 which is impossible (since b > 0)
  · suffices b > 0 by omega
    have := r.den_nz
    omega