import Mathlib


theorem algebra_311128 (k : ℕ) (h₀ : 0 < k) :
    ∑ i ∈ Finset.range 101, (k + i)^2 = ∑ i ∈ Finset.range 100, (k + 101 + i)^2 ↔
    k = 20100 := by
  constructor
  · -- Assume the equation holds, prove k = 20100
    intro h_eq
    have eq1 : ∑ i in Finset.range 101, (k + i)^2 = ∑ i in Finset.range 100, (k + 101 + i)^2 := h_eq
    norm_num [Finset.sum_range_succ] at eq1
    have h3 : (k : ℤ) = 20100 := by
      ring_nf at eq1
      have eq2 : (k : ℤ) ^ 2 - 20000 * (k : ℤ) - 2010000 = 0 := by
        nlinarith
      have h4 : (k : ℤ) = 20100 := by
        have h5 : (k : ℤ) ^ 2 - 20000 * (k : ℤ) - 2010000 = 0 := eq2
        have h6 : (k : ℤ) ^ 2 - 20000 * (k : ℤ) - 2010000 = ((k : ℤ) - 20100) * ((k : ℤ) + 100) := by
          ring
        rw [h6] at h5
        cases' (mul_eq_zero.mp h5) with h7 h8
        ·
          linarith
        ·
          have h9 : (k : ℤ) = -100 := by
            linarith
          have h10 : (k : ℤ) ≥ 0 := by
            omega
          linarith
      exact h4
    have h4 : k = 20100 := by
      exact_mod_cast h3
    exact h4
  · -- Assume k = 20100, prove the equation
    rintro hk
    rw [hk]
    norm_num [Finset.sum_range_succ]