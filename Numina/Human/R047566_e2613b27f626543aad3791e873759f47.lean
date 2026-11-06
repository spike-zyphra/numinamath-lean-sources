import Mathlib

/-Let d be a randomly chosen divisor of 2016. Find the expected value of
d^2 / (d^2 + 2016) -/

theorem number_theory_609606: ∑ d ∈ Nat.divisors 2016, ((1 / (Nat.divisors 2016).card) * ((d^2: ℚ) / (d^2 + 2016))) = 1 / 2 := by

  -- the key identity --
  have id: ∀ a: ℚ, a ≠ 0 →  a ^ 2 / (a ^ 2 + 2016) + (2016 / a) ^ 2 / ((2016 / a) ^ 2 + 2016) = 1 := by
    intro a
    intro ne
    field_simp
    ring_nf

  -- take out the common factor of 1/(Nat.divisors 2016).card --
  have sum_eq: 2 * (∑ d ∈ Nat.divisors 2016, ((d^2: ℚ) / (d^2 + 2016))) = ((Nat.divisors 2016).card: ℚ) := by
    let f: ℕ → ℚ := fun d => (d^2: ℚ) / (d^2 + 2016)

    -- write id in the form of f --
    have id_f: ∀ d: ℕ, d ∈ Nat.divisors 2016 → f d + f (2016 / d) = 1 := by
      intro d
      intro d_div
      have d_ne: d ≠ 0 := by
        by_contra! ne
        rw [ne] at d_div
        absurd d_div
        simp
      simp at d_div
      simp [f]
      specialize id (d: ℚ)
      simp [d_ne] at id
      have eq: ↑(2016 / d) = 2016 / (d: ℚ) := by
        rw [Rat.natCast_div]
        simp
        exact d_div
      rw [eq]
      exact id

    -- simplify the sum --
    have sum_f: ∑ d ∈ Nat.divisors 2016, ((d^2: ℚ) / (d^2 + 2016)) = ∑ d ∈ Nat.divisors 2016, f d := by
      simp [f]

    -- use the symmetry of d and 2016/d --
    have sum_f_eq: ∑ d ∈ Nat.divisors 2016, f (2016 / d) = ∑ d ∈ Nat.divisors 2016, f d := by
      apply Nat.sum_div_divisors

    simp [sum_f]
    calc
      2 * ∑ d ∈ Nat.divisors 2016, f d = ∑ d ∈ Nat.divisors 2016, f d + ∑ d ∈ Nat.divisors 2016, f d := by ring
                                      _ = ∑ d ∈ Nat.divisors 2016, f d + ∑ d ∈ Nat.divisors 2016, f (2016 / d) := by rw [sum_f_eq]
                                      _ =  ∑ d ∈ Nat.divisors 2016, (f d + f (2016 / d)) := by rw [←Finset.sum_add_distrib]
                                      _ =  ∑ d ∈ Nat.divisors 2016, 1 := by apply Finset.sum_congr;simp;simp;simp at id_f;exact id_f
                                      _ = ((Nat.divisors 2016).card: ℚ) := by simp

  -- take out the common factor of 1/(Nat.divisors 2016).card --
  have take_mul_Out: ∑ d ∈ Nat.divisors 2016, (1 / (Nat.divisors 2016).card) * ((d: ℚ) ^ 2 / (↑d ^ 2 + 2016))
   = (1 / ((Nat.divisors 2016).card : ℚ)) * ∑ d ∈ Nat.divisors 2016,  ((d: ℚ) ^ 2 / (↑d ^ 2 + 2016)) := by
    rw [Finset.mul_sum]

  rw [take_mul_Out]
  replace sum_eq: ∑ d ∈ Nat.divisors 2016, ((d^2: ℚ) / (d^2 + 2016)) = ((Nat.divisors 2016).card: ℚ) * 1/2 := by
    calc
      ∑ d ∈ Nat.divisors 2016, ((d^2: ℚ) / (d^2 + 2016)) = 2 * (∑ d ∈ Nat.divisors 2016, ((d^2: ℚ) / (d^2 + 2016))) / 2 := by simp
                                                        _  = ((Nat.divisors 2016).card: ℚ) / 2 := by rw [sum_eq]
                                                        _  = ((Nat.divisors 2016).card: ℚ) * 1/2 := by simp

  rw [sum_eq]
  field_simp