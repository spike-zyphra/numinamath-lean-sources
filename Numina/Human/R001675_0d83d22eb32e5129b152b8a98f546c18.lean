import Mathlib

open Real

/- 4. (GBR 1a) ${ }^{\mathrm{IMO} 6}$ For all positive integral $n$, $u_{n+1}=u_{n}\left(u_{n-1}^{2}-2\right)-u_{1}$, $u_{0}=2$, and $u_{1}=5 / 2$. Prove that  $$ 3 \log_{2}\left[u_{n}\right]=2^{n}-(-1)^{n} $$  where $[x]$ is the integral part of $x$. -/
theorem algebra_25091 {u : ℕ → ℝ} (hu0 : u 0 = 2) (hu1 : u 1 = 5 / 2)
    (hun : ∀ n : ℕ, u (n + 2) = u (n + 1) * ((u n)^2 - 2) - u 1) :
    ∀ n > 0, 3 * logb 2 (⌊u n⌋) = 2^n - (-1)^n := by
  let r (n : ℕ) : ℝ := (2^n - (-1)^n) / 3
  -- Define r(n) = (2^n - (-1)^n) / 3, and prove by induction that u_n = 2^r(n) + 2^(-r(n))
  have h : ∀ n, u n = 2 ^ (r n) + 2 ^ (- r n) := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    cases' n with n
    · simp [hu0, r]
      norm_num
    cases' n with n
    · simp [hu1, r]
      norm_num
    rw [hun, ih _ (by omega), ih _ (by omega), hu1]
    ring_nf
    have h1 : ∀ x : ℝ, 2^x * (2 : ℝ) = 2 ^ (x + 1) := by
      intro x
      rw [rpow_add (by norm_num)]
      simp
    have h2 : ∀ x : ℝ, ((2 : ℝ)^x)^2 = 2^(x * 2) := by
      intro x
      rw [rpow_mul (by norm_num)]
      simp
    have h3 : ∀ x y : ℝ, (2 : ℝ)^x * 2^y = 2^(x + y) := by
      intro x y
      rw [rpow_add (by norm_num)]
    simp only [h1, h2, h3]
    ring_nf
    rcases Nat.even_or_odd n with h_even | h_odd
    · simp [h_even.neg_one_pow]
      norm_num1
      ring_nf
    · simp [h_odd.neg_one_pow]
      norm_num1
      ring_nf
  intro n hn
  -- Now we need to prove that 3*logb 2 (⌊u n⌋) = 2^n - (-1)^n
  -- Prove that r(n) > 0 for n > 0, which will be needed to show 2^(-r(n)) < 1
  have hr : 0 < r n := by
    simp [r]
    apply lt_of_le_of_lt (b := 1)
    · rcases Nat.even_or_odd n with h_even | h_odd
      · simp [h_even.neg_one_pow]
      · simp [h_odd.neg_one_pow]
    apply one_lt_pow₀
    · norm_num
    · omega
  -- Prove that ⌊u_n⌋ = ⌊2^r(n) + 2^(-r(n))⌋ = 2^r(n) since 2^(-r(n)) < 1
  have h_floor : ⌊(2 : ℝ) ^ r n + 2 ^ (-r n)⌋ = (2 : ℝ) ^ r n := by
    obtain ⟨rn, hrn⟩ : ∃ rn : ℕ, r n = rn := by
      simp [r]
      have h_dvd : 3 ∣ 2^n - (-1)^n := by
        rw [← Int.modEq_iff_dvd]
        gcongr
        rw [Int.modEq_iff_dvd]
        norm_num
      rcases Nat.even_or_odd n with h_even | h_odd
      · use (2^n - 1) / 3
        simp [h_even.neg_one_pow] at h_dvd ⊢
        suffices ((2 ^ n - 1) / 3 : ℝ) = (((((2 ^ n - 1) / 3) : ℕ) : ℚ) : ℝ) by
          simp [this]
        rw [Rat.natCast_div]
        · simp
        zify [Nat.one_le_two_pow]
        assumption
      · use (2^n + 1) / 3
        simp [h_odd.neg_one_pow] at h_dvd ⊢
        suffices ((2 ^ n + 1) / 3 : ℝ) = (((((2 ^ n + 1) / 3) : ℕ) : ℚ) : ℝ) by
          simp [this]
        rw [Rat.natCast_div]
        · simp
        zify
        assumption
    rw [hrn]
    simp
    have : (2 : ℝ) ^ rn = (2 ^ rn : ℤ) := by
      rify
    rw [this, Int.cast_inj, Int.floor_eq_iff]
    constructor
    · simp
      apply rpow_nonneg
      norm_num
    · simp [← hrn]
      apply rpow_lt_one_of_one_lt_of_neg
      · norm_num
      simp [hr]
  -- Using the above, we complete the proof
  rw [h, h_floor]
  simp [r]
  ring_nf
