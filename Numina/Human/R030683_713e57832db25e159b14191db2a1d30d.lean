import Mathlib

/- 7. The sum of the reciprocals of all positive integers $n$ that make $\left[\frac{n^{2}}{5}\right]$ a prime number is . $\qquad$ -/
theorem number_theory_234188 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ Prime ⌊(n ^ 2 : ℝ) / 5⌋}, (1 : ℚ) / n = 37 / 60 := by
  set s := {n : ℕ | _}
  -- It is enough to show that the set from the theorem statement is equal to {4, 5, 6}.
  suffices s = {4, 5, 6} by
    rw [this, finsum_mem_eq_toFinset_sum]
    simp
    norm_num
  ext n
  simp [s, Int.prime_iff_natAbs_prime]
  symm
  constructor
  -- Show that n ∈ {4, 5, 6} implies that ⌊n ^ 2 / 5⌋ is prime.
  · intro h
    rcases h with hn | hn | hn <;> subst n <;> norm_num
  -- Show that if ⌊n^2 / 5⌋ is prime then n = 4, n = 5, or n = 6.
  intro ⟨hn_pos, hp⟩
  -- Consider two cases: n ≤ 7 and 8 ≤ n.
  cases' show n ≤ 7 ∨ 8 ≤ n by omega with hn hn
  -- If n ≤ 7 then consider all possible values of n and find out that
  -- ⌊n^2 / 5⌋ is prime for n ∈ {4, 5, 6} only.
  · interval_cases n <;> norm_num at hp ⊢
  -- Now assume that 8 ≤ n.
  -- Show that there exist k and r such that
  -- n = 5 * k + r, 2 ≤ k, -2 ≤ r ≤ 2.
  have ⟨k, r, hn, hk, hr1, hr2⟩ : ∃ (k : ℕ) (r : ℤ), n = 5 * k + r ∧ 2 ≤ k ∧ -2 ≤ r ∧ r ≤ 2 := by
    -- Consider special cases n = 8 and n = 9.
    rcases show n = 8 ∨ n = 9 ∨ 10 ≤ n by omega with hn | hn | hn
    -- If n = 8 then take k = 2 and r = -2.
    · use 2, -2
      norm_num [hn]
    -- If n = 9 then take k = 2 and r = -1.
    · use 2, -1
      norm_num [hn]
    -- Now we have 10 ≤ n.
    -- We can find k and r such that n = 5 * k + r, 2 ≤ k and 0 ≤ r < 5.
    have ⟨k, r, hnkr, hk, hr⟩ : ∃ (k : ℕ) (r : ℕ), n = 5 * k + r ∧ 2 ≤ k ∧ r < 5 := by
      use n / 5, n % 5
      simp [Nat.div_add_mod, Nat.mod_lt]
      omega
    -- Consider two cases: r ≤ 2 and 3 ≤ r.
    cases' show r ≤ 2 ∨ 3 ≤ r by omega with hr hr
    -- If r ≤ 2 then k and r satisfy all requirements.
    · use k, r
      simp [hnkr, hr, hk]
      linarith
    -- If 3 ≤ r then k + 1 and r - 5 satisfy all requirements.
    · use k + 1, r - 5
      simp [hnkr]
      constructorm* _ ∧ _ <;> linarith
  -- Show that ⌊n^2 / 5⌋ is not prime for 8 ≤ n.
  contrapose hp
  -- We have n^2 / 5 = k * (5 * k + 2 * r) + r^2 / 5.
  have eq : (n : ℝ)^2 / 5 = (k * (5 * k + 2 * r) : ℤ) + r ^ 2 / 5 := by
    rw [show (n : ℝ) = (n : ℤ) by simp, hn]
    push_cast
    ring
  -- ⌊r ^ 2 / 5⌋ = 0 because |r| ≤ 2 and 0 ≤ r^2 / 5 < 1.
  have eq2 : ⌊(r ^ 2 : ℝ) / 5⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    simp only [Set.mem_Ico]
    refine ⟨by positivity, ?_⟩
    suffices (r : ℝ) ^ 2 ≤ 2^2 by linarith
    simp [sq_le_sq, abs_le']
    rify at hr1 hr2
    exact ⟨hr2, by linarith⟩
  -- We get ⌊n^2 / 5⌋ = k * (5 * k + 2 * r) + ⌊r^2 / 5⌋ = k * (5 * k + 2 * r).
  rw [eq, Int.floor_int_add, eq2]
  simp [Int.natAbs_mul]
  -- k * (5 * k + 2 * r) is not prime because k > 1 and 5 * k + 2 * r > 1.
  apply Nat.not_prime_mul (by omega)
  zify
  suffices 5 * k + r ≥ 2 by rw [abs_of_nonneg (by omega)]; linarith
  linarith