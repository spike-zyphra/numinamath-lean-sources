import Mathlib

/- 27. N5 (BUL) ${ }^{\mathrm{IMO} 6}$ Let $a>b>c>d$ be positive integers and suppose  $$ a c+b d=(b+d+a-c)(b+d-a+c) . $$  Prove that $a b+c d$ is not prime. -/
theorem number_theory_25084 (a b c d : ℤ) (h₀ : a > b) (h₁ : b > c) (h₂ : c > d) (h₃ : d > 0) (h : a * c + b * d = (b + d + a - c) * (b + d - a + c)) :
    ¬Prime (a * b + c * d) := by
  -- The given equality is equivalent to a² - ac + c² = b² + bd + d².
  have h₄ : a ^ 2 - a * c + c ^ 2 = b ^ 2 + b * d + d ^ 2 := by
    linarith
  -- Therefore, (ab + cd)(ad + bc) = (ac + bd)(a² - ac + c²).
  have h₅ : (a * b + c * d) * (a * d + b * c) = (a * c + b * d) * (a ^ 2 - a * c + c ^ 2) := by
    calc
      _ = (a * c) * (b ^ 2 + b * d + d ^ 2) + (b * d) * (a ^ 2 - a * c + c ^ 2) := by ring
      _ = (a * c) * (a ^ 2 - a * c + c ^ 2) + (b * d) * (a ^ 2 - a * c + c ^ 2) := by rw [h₄]
      _ = (a * c + b * d) * (a ^ 2 - a * c + c ^ 2) := by ring
  -- Suppose on the contray that ab + cd is a prime.
  by_contra hp
  -- Note that a ^ 2 - ac + c ^ 2 > 0.
  have h₆ : a ^ 2 - a * c + c ^ 2 > 0 := by
    nlinarith
  -- We have ab + cd > ac + bd > ad + bc ≥ 1.
  have h₇ : a * b + c * d > a * c + b * d := by
    nlinarith
  have h₈ : a * c + b * d > 1 := by
    nlinarith
  -- Since ab + cd is a prime and 1 < ac + bd < ab + cd, it is coprime with ac + bd.
  have h₉ : IsCoprime (a * b + c * d) (a * c + b * d) := by
    -- Convert the problem to natural numbers.
    rw [Int.coprime_iff_nat_coprime]
    -- Assume on the contrary that a * b + c * d is not coprime with a * c + b * d, then ac + bd ∣ ab + cd.
    by_contra!
    rw [Nat.Prime.coprime_iff_not_dvd (by rw [Nat.prime_iff_prime_int]; simp [hp, Prime.abs]), not_not] at this
    -- We have ab + cd ≤ ac + bd, which is a contradiction.
    apply Nat.le_of_dvd (by positivity) at this
    omega
  -- Therefore, we have ac + bd ∣ ad + bc.
  replace h₅ : a * c + b * d ∣ (a * b + c * d) * (a * d + b * c) := by
    -- This is a direct consequence of the h₅.
    rw [h₅]
    apply dvd_mul_right
  apply IsCoprime.dvd_of_dvd_mul_left (h₉.symm) at h₅
  -- However, we have ac + bd > ad + bc > 0, so we contradicts with the divisibility.
  rw [<-Int.natAbs_dvd_natAbs] at h₅
  have h₁₀ : a * d + b * c > 0 := by
    nlinarith
  apply Nat.le_of_dvd (by positivity) at h₅
  replace h₉ : a * c + b * d > a * d + b * c := by
    nlinarith
  omega
    
