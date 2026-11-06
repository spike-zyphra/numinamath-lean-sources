import Mathlib

theorem number_theory_218459 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : p + q = r) (hqr' : 1 < p ∧ p < q) :
    p = 2 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  by_cases h : p % 2 = 1
  · -- Assume p is odd, so p is an odd prime. Then r = p + q would have to be even
    -- contradiction because p + q would be even prime >= 2k > 2.
    -- The code here would develop the contradiction directly.
    have hp2 : p % 2 = 1 := h
    by_cases h4 : q % 2 = 1
    · -- Assume q is odd
      have : r % 2 = 0 := by
        -- r = p + q
        -- p % 2 = 1
        -- q % 2 = 1
        have : r = p + q := by
          omega
        rw [this]
        omega
      have : r > 2 := by
        -- r = p + q >= 3 + 3 = 6 > 2
        nlinarith [hqr'.left, hqr'.right, Nat.Prime.two_le hp, Nat.Prime.two_le hq]
      have : ¬ r.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
        all_goals linarith
      contradiction
    · -- Assume q is even
      have h4 : q % 2 = 0 := by omega
      have h4 : q = 2 := by
        -- q is even and q is a prime means q is 2
        by_cases h5 : q > 2
        · -- q must be even and > 2 then it is not a prime. Contradiction
          have h6 : ¬ q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
            all_goals linarith
          contradiction
        · -- q <= 2
          interval_cases q <;> try tauto
      -- q = 2 and p < q becomes p < 2
      have : p < 2 := by
        linarith [h4, hqr'.right]
      omega
  · -- p % 2 = 0
    have hp2 : p % 2 = 0 := by omega
    have : p = 2 := by
      -- p is even and p is a prime means p is 2
      by_cases h5 : p > 2
      · -- p must be even and > 2 then it is not a prime. Contradiction
        have h6 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals linarith
        contradiction
      · -- p <= 2
        interval_cases p <;> tauto
    assumption