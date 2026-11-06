import Mathlib

/- ## Problem 1

$\mathrm{n}>1$, and $\mathrm{a}$ and $\mathrm{b}$ are positive real numbers such that $\mathrm{a}^{\mathrm{n}}-\mathrm{a}-1=0$ and $\mathrm{b}^{2 \mathrm{n}}-\mathrm{b}-3 \mathrm{a}=0$. Which is larger?

 -/
theorem algebra_210640 (n : ℕ) (a b : ℝ) (h₀ : n > 1) (h₁ : 0 < a) (h₂ : 0 < b)
    (h₃ : a ^ n - a - 1 = 0) (h₄ : b ^ (2 * n) - b - 3 * a = 0) :
    a > b := by
    --assume by contradiction that b > a
    by_contra h
    push_neg at h
    --one has that a ^ 2n = (a ^ n) ^ 2 = (a + 1) ^ 2 = a ^ 2 + 2a * 1
    have a_pow_two_n : a ^ (2 * n) = a ^ 2 + 2 * a + 1 := by
      rw[(by ring_nf : (1 : ℝ) = 1 ^ 2)]
      nth_rw 3 [(by ring_nf : a = a * 1)]
      rw[← mul_assoc, ← add_sq a 1, mul_comm, pow_mul]
      suffices a ^ n = a + 1 by
        rw[sq_eq_sq (by linarith) (by linarith)]
        exact this
      linarith
    --moreover a ^ 2n is bounded by 4a because a^2 + 1 is bounded by 2a
    have bound_a : a ^ (2 * n) > 4 * a := by 
      suffices a ^ 2 + 1 > 2 * a by
        rw[a_pow_two_n, add_assoc, add_comm (2 * a), ← add_assoc]
        rw[(by linarith : 4 * a = 2 * a + 2 * a)]
        linarith
      have a_gt_one : a > 1 := by 
        by_contra kk 
        push_neg at kk
        have : a ^ n > 1 := by
          calc a ^ n
          _ = a + 1 := by linarith
          _ > 1 := by linarith
        by_contra hk
        push_neg at hk
        have contr : a ^ n ≤ 1 := by
          exact pow_le_one₀ (le_of_lt h₁) kk
        linarith
      --to do so one writes a = 1 + (a + 1) and developes the square of the sum in a ^ 2 + 1, finding the bound
      calc a ^ 2 + 1 
        = 1 + 2 * (a - 1) + (a - 1) ^ 2 + 1 := by nth_rw 1 [(by ring_nf : a = 1 + (a - 1))]; rw[add_sq]; ring_nf
        _ > 2 + 2 * (a - 1) := by
          suffices (a - 1) ^ 2 > 0 by
            linarith
          exact sq_pos_of_pos (by linarith)
        _ = 2 * a := by linarith
    --b ^ 2n = b + 3a by hypotheses
    have b_pow_n : b ^ (2 * n) = b + 3 * a := by linarith
    --then the ratio of b^2n over a ^ 2n is less than the ratio of the two bounds.
    have div_b_a : (b / a) ^ (2 * n) < (b + 3 * a) / (4 * a) := by
      rw[div_pow]
      refine div_lt_div' (by linarith) (by linarith) (by linarith) (by linarith)
    --this leads to (b/a)^2n < b/a via a chain of estimates
    have hyp1 : (b / a) ^ (2 * n) < (b / a) := by
      suffices (b + 3 * a) / (4 * a) ≤ (b / a) by
        linarith
      calc (b + 3 * a) / (4 * a)
      _ ≤ (b + 3 * b) / (4 * a) := by 
        have : b + 3 * a ≤ b + 3 * b := by linarith
        exact (div_le_div_right (by linarith)).mpr this
      _ = b / a := by ring_nf
    --however this is contradiction, because by assumption we had b/a ≥ 1 leading to b/a^2n ≥ b/a
    have hyp2 : (b / a) ^ (2 * n) ≥ (b / a) := by 
      nth_rw 2 [← pow_one (b / a)]
      exact pow_le_pow_right (by rw[← one_le_div h₁] at h; exact h) (by linarith)
    linarith