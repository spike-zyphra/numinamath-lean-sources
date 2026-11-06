import Mathlib

/- A standard six-sided die is rolled, and  $P$ is the product of the five numbers that are visible. What is the largest number that is certain to divide $P$? -/
theorem number_theory_15987 : IsGreatest { d : ℕ | d ∣ 2 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 5 } 12 := by
  -- Rewrite the 6 conditions as a single condition
  have H1 d : d ∣ 2 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 5 ↔ ∀ a ∈ ({ 2 * 3 * 4 * 5 * 6, 1 * 3 * 4 * 5 * 6, 1 * 2 * 4 * 5 * 6, 1 * 2 * 3 * 5 * 6, 1 * 2 * 3 * 4 * 6, 1 * 2 * 3 * 4 * 5 } : Multiset ℕ), d ∣ a := by
    simp
  -- Use the lemma:
  -- d | s.gcd ↔ ∀ a ∈ s, d | a
  have H2 d : (∀ a ∈ ({ 2 * 3 * 4 * 5 * 6, 1 * 3 * 4 * 5 * 6, 1 * 2 * 4 * 5 * 6, 1 * 2 * 3 * 5 * 6, 1 * 2 * 3 * 4 * 6, 1 * 2 * 3 * 4 * 5 } : Multiset ℕ), d ∣ a) ↔ d ∣ ({ 2 * 3 * 4 * 5 * 6, 1 * 3 * 4 * 5 * 6, 1 * 2 * 4 * 5 * 6, 1 * 2 * 3 * 5 * 6, 1 * 2 * 3 * 4 * 6, 1 * 2 * 3 * 4 * 5 } : Multiset ℕ).gcd := by
    rw [Multiset.dvd_gcd]
  -- Rewrite and simplify
  rw [Set.ext H1, Set.ext H2]
  simp
  -- Now we need to compute the gcd of the multiset
  have H3 : gcd 720 (gcd 360 (gcd 240 (gcd 180 (gcd 144 120)))) = 12 := by
    -- Step by step computation
    -- The usage of decide is necessary to simplify the gcd of two numbers, and can be replaced by the actual computation
    calc _ = gcd 720 (gcd 360 (gcd 240 (gcd 180 24))) := by rw [show gcd 144 120 = 24 by decide]
         _ = gcd 720 (gcd 360 (gcd 240 12)) := by rw [show gcd 180 24 = 12 by decide]
         _ = gcd 720 (gcd 360 12) := by rw [show gcd 240 12 = 12 by decide]
         _ = gcd 720 12 := by rw [show gcd 360 12 = 12 by decide]
         _ = 12 := by decide
  rw [H3]
  -- Trivial proof that 12 is the greatest divisor of 12
  constructor
  . use 1
  . intro d hd
    simp at hd
    obtain ⟨c, hd⟩ := hd
    have hc : c ≥ 1 := by
      by_contra!
      interval_cases c
      trivial
    nlinarith
