import Mathlib

open Real

theorem inequalities_308523 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x ^ n + y ^ n) / 2 ≥ ((x + y) / 2) ^ n := by

  have h3 : ∀ n : ℕ, ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h4 : ((x + y) / 2) ^ (n + 1) ≤ (x ^ (n + 1) + y ^ (n + 1)) / 2 := by
        have h5 : ((x + y) / 2) ^ (n + 1) = ((x + y) / 2) * ((x + y) / 2) ^ n := by ring
        rw [h5]
        have h7 : ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := ih
        have h8 : ((x + y) / 2) * ((x + y) / 2) ^ n ≤ ((x + y) / 2) * ((x ^ n + y ^ n) / 2) := by
          apply mul_le_mul_of_nonneg_left
          linarith
          all_goals linarith
        have h9 : ((x + y) / 2) * ((x ^ n + y ^ n) / 2) ≤ (x ^ (n + 1) + y ^ (n + 1)) / 2 := by
          have h10 : ((x + y) / 2) * ((x ^ n + y ^ n) / 2) ≤ (x ^ (n + 1) + y ^ (n + 1)) / 2 := by
            have h12 : ((x + y) / 2) * (x ^ n + y ^ n) ≤ x ^ (n + 1) + y ^ (n + 1) := by
              have h13 : (x ^ (n + 1) + y ^ (n + 1)) - ((x + y) / 2) * (x ^ n + y ^ n) ≥ 0 := by
                have h14 : (x ^ (n + 1) + y ^ (n + 1)) - ((x + y) / 2) * (x ^ n + y ^ n) = (x ^ n * (x - y) - y ^ n * (x - y)) / 2 := by ring_nf
                rw [h14]
                have h15 : x ^ n * (x - y) - y ^ n * (x - y) ≥ 0 := by
                  have h16 : x ^ n * (x - y) - y ^ n * (x - y) = (x ^ n - y ^ n) * (x - y) := by ring
                  rw [h16]
                  have h17 : (x ^ n - y ^ n) * (x - y) ≥ 0 := by
                    by_cases hxy : x ≥ y
                    ·
                      have h8 : x ^ n ≥ y ^ n := by
                        apply pow_le_pow_left
                        all_goals linarith
                      have h9 : (x ^ n - y ^ n) ≥ 0 := by
                        linarith
                      have h10 : (x - y) ≥ 0 := by linarith
                      nlinarith
                    ·
                      have hxy' : y ≥ x := by linarith
                      have h11 : x ^ n ≤ y ^ n := by
                        apply pow_le_pow_left
                        all_goals linarith
                      have h12 : (x ^ n - y ^ n) ≤ 0 := by
                        linarith
                      have h13 : (x - y) ≤ 0 := by linarith
                      nlinarith
                  linarith
                linarith
              linarith
            linarith
          linarith
        linarith
      linarith
  specialize h3 n
  linarith