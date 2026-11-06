import Mathlib


theorem algebra_266442 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, i^3 = (∑ i in Finset.Icc 1 n, i)^2 := by
  have h2 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, i ^ 3 = (∑ i in Finset.Icc 1 n, i) ^ 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      have h3 : ∑ i in Finset.Icc 1 k, i ^ 3 = (∑ i in Finset.Icc 1 k, i) ^ 2 := by
        apply ih
      have eq1 : (∑ i in Finset.Icc 1 k, i ^ 3 : ℕ) + (k + 1 : ℕ) ^ 3 = (∑ i in Finset.Icc 1 k, i + (k + 1 : ℕ)) ^ 2 := by
        have eq24 : (k * (k + 1 : ℕ) / 2 : ℕ) ^ 2 + (k + 1 : ℕ) ^ 3 = ((k * (k + 1 : ℕ) / 2 + (k + 1 : ℕ)) : ℕ) ^ 2 := by
          have eq25 : ((k * (k + 1 : ℕ) / 2 + (k + 1 : ℕ)) : ℕ) ^ 2 = (k * (k + 1 : ℕ) / 2 : ℕ) ^ 2 + 2 * ((k * (k + 1 : ℕ) / 2 : ℕ) * (k + 1 : ℕ)) + (k + 1 : ℕ) ^ 2 := by
            ring
          rw [eq25]
          have eq26 : 2 * ((k * (k + 1 : ℕ) / 2 : ℕ) * (k + 1 : ℕ)) + (k + 1 : ℕ) ^ 2 = (k + 1 : ℕ) ^ 3 := by
            have eq27 : (k * (k + 1 : ℕ) % 2 = 0) := by
              have : k % 2 = 0 ∨ k % 2 = 1 := by omega
              rcases this with (h | h)
              · 
                simp [Nat.mul_mod, Nat.add_mod, h]
              · 
                simp [Nat.mul_mod, Nat.add_mod, h]
            have eq28 : (k * (k + 1 : ℕ) / 2 : ℕ) * 2 = k * (k + 1 : ℕ) := by
              omega
            nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k + 1 : ℕ) : ℕ)]
          nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k + 1 : ℕ) : ℕ)]
        have eq3 : (k * (k + 1 : ℕ) / 2 : ℕ) = ∑ i in Finset.Icc 1 k, i := by
          have h1 : ∀ k : ℕ, ∑ i in Finset.Icc 1 k, (i : ℕ) = k * (k + 1) / 2 := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              rw [Finset.sum_Icc_succ_top (by omega)]
              rw [ih]
              ring_nf
              omega
          have h10 : ∑ i in Finset.Icc 1 k, (i : ℕ) = k * (k + 1) / 2 := h1 k
          omega
        rw [eq3] at eq24
        nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k + 1 : ℕ) : ℕ)]
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k + 1 : ℕ) : ℕ)]
  exact h2 n