import Mathlib

/- Find the largest integer that divides $m^{5}-5 m^{3}+4 m$ for all $m \geq 5$. -/
theorem algebra_610924 :
    IsGreatest {d : ℤ | ∀ m ≥ 5, d ∣ m ^ 5 - 5 * m ^ 3 + 4 * m} 120 := by
  constructor
  -- First, we prove that 120 ∣ m^5 - 5m^3 + 4m for all m ≥ 5
  . intro m hm
    -- m^5 - 5m^3 + 4m = (m-2)(m-1)m(m+1)(m+2)
    -- As m - 2 ≥ 0, we can lift m - 2 to a natural number
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = m - 2 := CanLift.prf (m - 2) (show 0 ≤ m - 2 by linarith)
    -- And m^5 - 5m^3 + 4m = ascFactorial k 5
    -- So 120 = 5! divides m^5 - 5m^3 + 4m
    have H := Nat.factorial_dvd_ascFactorial k 5
    simp [Nat.factorial, Nat.ascFactorial] at H
    zify at H
    rw [hk] at H
    convert H using 1
    ring
  -- Next, we prove that any integer d that divides m^5 - 5m^3 + 4m for all m ≥ 5 must be ≤ 120
  . intro d hd
    simp at hd
    -- Set m = 5 and m = 24 we get
    -- d ∣ 2520 and d ∣ 7893600
    have h₁ := hd 5 (by simp)
    have h₂ := hd 24 (by simp)
    simp at h₁ h₂
    -- So d ∣ gcd 2520 7893600, which is 120
    have h₃ : d ∣ gcd 2520 7893600 := dvd_gcd h₁ h₂
    simp [gcd, Int.gcd] at h₃
    exact Int.le_of_dvd (by simp) h₃
