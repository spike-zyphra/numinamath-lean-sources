import Mathlib

set_option maxHeartbeats 1000000


theorem number_theory_98643 :
    IsGreatest {p : ℕ | p.Prime ∧ p < 1000 ∧ ∃ z : ℂ, ∃ a b : ℤ,
      z.re = a ∧ z.im = b ∧ Complex.abs z = Real.sqrt p ∧
      (z ^ 3).re > 0 ∧ (z ^ 3).im > 0 ∧ (z ^ 3).re + (z ^ 3).im > p ∧
      (z ^ 3).re + p > (z ^ 3).im ∧ (z ^ 3).im + p > (z ^ 3).re} 349 := by
  have hi3 : Complex.I ^ 3 = -.I := by
    rw [show 3 = 2 + 1 by norm_num, pow_succ, Complex.I_sq, neg_one_mul]
  simp only [IsGreatest, gt_iff_lt, Set.mem_setOf_eq, upperBounds, and_imp]
  constructor
  .
    norm_num
    use 18 + 5 * .I
    simp [Complex.abs, Complex.normSq]
    refine ⟨⟨18, rfl⟩, ⟨5, rfl⟩, by norm_num, ?_⟩
    have eq : (18 + 5 * .I : Complex) ^ 3 = 4482 + 4735 * .I := by
      ring_nf
      rw [hi3, Complex.I_sq]
      ring
    simp [eq]
    norm_num
  intro p hp hp2 ⟨z, a, b, hza, hzb, hzp, hz1, hz2, hz3, hz4, hz5⟩
  have hz_eq : z = a + b * .I := by apply Complex.ext <;> simp [hza, hzb]
  have hz3_eq : z ^ 3 = a * (a ^ 2 - 3 * b ^ 2) + b * (3 * a ^ 2 - b ^ 2) * .I := by
    rw [hz_eq]
    ring_nf
    rw [hi3, Complex.I_sq]
    ring
  have hz3_re : (z ^ 3).re = a * (a ^ 2 - 3 * b ^ 2) := by
    simp [hz3_eq]
    norm_cast
    simp
  have hz3_im : (z ^ 3).im = b * (3 * a ^ 2 - b ^ 2) := by
    simp [hz3_eq]
    norm_cast
    simp
  have hp_eq : p = a ^ 2 + b ^ 2 := by
    simp [hz_eq, Complex.abs, Complex.normSq] at hzp
    rify
    rw [← Real.sqrt_inj (by positivity) (by positivity)]
    rw [← hzp, pow_two, pow_two]
  simp [hz3_re, hz3_im] at hz1 hz2 hz3 hz4 hz5
  clear hz_eq hz3_eq hz3_re hz3_im hzp hza hzb
  norm_cast at hz1 hz2 hz3 hz4 hz5
  have hineq : |(a + b) * (a ^ 2 - 4 * a * b + b ^ 2)| ≤ a ^ 2 + b ^ 2 := by
    rw [show (a + b) * (a ^ 2 - 4 * a * b + b ^ 2) = a * (a ^ 2 - 3 * b ^ 2) - b * (3 * a ^ 2 - b ^ 2) by ring]
    rw [abs_sub_le_iff]
    constructor <;> linarith
  clear hz3 hz4 hz5 hi3
  have ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by
    constructor
    .
      contrapose! hz1
      simp [hz1]
    .
      contrapose! hz2
      simp [hz2]
  by_cases hab : a + b = 0
  .
    suffices p = 2 by linarith
    apply ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp _).symm
    zify
    simp only [hp_eq, show b = -a by linarith, even_two, Even.neg_pow, ← two_mul]
    use a ^ 2
  have hab2 : 0 < a * b := by
    contrapose! hineq
    calc
      a ^ 2 + b ^ 2 < 1 * (a ^ 2 - (-1) + b ^ 2) := by linarith
      _ ≤ |a + b| * (a ^ 2 - 4 * a * b + b ^ 2) := by
          gcongr
          .
            linarith
          .
            rw [le_abs]
            omega
          .
            suffices 4 * (a * b) < 0 by rw [mul_assoc]; omega
            apply mul_neg_of_pos_of_neg (by norm_num)
            suffices a * b ≠ 0 by omega
            apply mul_ne_zero ha0 hb0
      _ = |(a + b) * (a ^ 2 - 4 * a * b + b ^ 2)| := by
          rw [abs_mul]
          congr
          rw [abs_of_nonneg (by linarith)]
  wlog hab_pos : 0 < a ∧ 0 < b generalizing a b
  .
    apply this (-b) (-a)
    .
      simp [hp_eq, add_comm]
    .
      linarith
    .
      linarith
    .
      rw [show (-b + -a) * ((-b)^2 - 4 * -b * -a + (-a)^2) = -((a + b) * (a^2 - 4 * a * b + b ^ 2)) by ring]
      simpa [add_comm (b ^ 2)] using hineq
    .
      omega
    .
      omega
    .
      omega
    .
      simpa [mul_comm] using hab2
    .
      simp [mul_pos_iff] at hab2
      omega
  clear ha0 hb0 hab2 hab
  lift a to ℕ using le_of_lt hab_pos.1
  lift b to ℕ using le_of_lt hab_pos.2
  norm_cast at hp_eq hab_pos
  have hab1 : 3 * b^2 < a^2 := by
    zify at hab_pos ⊢
    simp [mul_pos_iff, hab_pos] at hz1
    exact hz1
  clear hz1 hz2
  have habp : Nat.Coprime a b := by
    by_contra h
    rw [Nat.Prime.not_coprime_iff_dvd] at h
    have ⟨q, hq, hqa, hqb⟩ := h
    have hqa2 := dvd_pow hqa (n := 2) (by norm_num)
    have hqb2 := dvd_pow hqb (n := 2) (by norm_num)
    have eq : q = p := by
      rw [← Nat.prime_dvd_prime_iff_eq hq hp]
      rw [hp_eq]
      exact Nat.dvd_add hqa2 hqb2
    contrapose! hp_eq
    apply ne_of_lt
    rw [← eq]
    calc
      q < q + q := by linarith [hq.pos]
      _ ≤ a ^ 2 + b ^ 2 := by
          apply add_le_add (Nat.le_of_dvd (by omega) hqa2) (Nat.le_of_dvd _ hqb2)
          apply pow_pos hab_pos.2
  by_contra! hp1
  have hb1 : 5 ≤ b := by
    by_contra! hb2
    have ha1 : 19 ≤ a := by nlinarith
    contrapose! hineq
    zify at ha1 hb2 hp2
    calc
      (a ^ 2 + b ^ 2 : ℤ) < 19 * (19 * 3) := by linarith
      _ ≤ (a + b) * (a^2 - 4 * a * 4 + 0) := by
          gcongr
          linarith
          rw [show (a ^ 2 - 4 * a * 4 + 0 : ℤ) = a * (a - 16) by ring]
          gcongr
          linarith
      _ ≤ (a + b) * (a^2 - 4 * a * b + b^2) := by
          gcongr
          linarith
          positivity
      _ ≤ |(a + b : ℤ) * (a^2 - 4 * a * b + b ^ 2)| := le_abs_self _
  have hineq2 : |(a ^ 2 - 4 * a * b + b ^ 2 : ℤ)| ≤ a + b := by
    zify at hab_pos
    apply Int.le_of_mul_le_mul_left (a := a + b) _ (by linarith)
    calc
      (a + b : ℤ) * |(a^2 - 4 * a * b + b^2 : ℤ)| = |(a + b : ℤ) * (a^2 - 4 * a * b + b^2)| := by
          rw [abs_mul, eq_comm, abs_of_nonneg (by linarith)]
      _ ≤ a^2 + b^2 := hineq
      _ ≤ (a + b) * (a + b) := by nlinarith
  rw [abs_le'] at hineq2
  have h1 : a ^ 2 + b ^ 2 ≤ 4 * a * b + a + b := by
    zify
    linear_combination hineq2.1
  have h2 : 4 * a * b ≤ a + b + a ^ 2 + b ^ 2 := by
    zify
    linear_combination hineq2.2
  clear hineq2
  have hb2 : b ≤ 8 := by nlinarith
  subst p
  interval_cases b
  ·
    replace ha2 : a ≤ 20 := by nlinarith
    have ha1 : 19 ≤ a := by nlinarith
    interval_cases a <;> norm_num at hp
  ·
    replace ha2 : a ≤ 23 := by nlinarith
    have ha1 : 21 ≤ a := by nlinarith
    interval_cases a <;> norm_num at hp
  ·
    replace ha2 : a ≤ 27 := by nlinarith
    have ha1 : 25 ≤ a := by nlinarith
    interval_cases a <;> norm_num at hp
  ·
    replace ha2 : a ≤ 30 := by nlinarith
    have ha1 : 29 ≤ a := by nlinarith
    interval_cases a <;> norm_num at hp