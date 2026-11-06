import Mathlib

theorem algebra_94026 (a : ℕ → ℝ) (ha1 : a 1 = 1) (han : ∀ n ≥ 1, (a (n + 1)) ^ 3 = 99 * (a n) ^ 3) :
    a 100 = 99 ^ 33 := by
  have h2 : ∀ n, a (n + 1) ^ 3 = 99 ^ n * (a 1) ^ 3 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h3 : a (n + 2) ^ 3 = 99 * (a (n + 1)) ^ 3 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [h3]
      rw [ih]
      ring
  have h4 : a 100 ^ 3 = 99 ^ 99 := by
    have h5 : a 100 ^ 3 = 99 ^ 99 * (a 1) ^ 3 := by
      specialize h2 99
      simpa using h2
    rw [h5, ha1]
    norm_num
  have h5 : ∀ (n : ℕ), a (n + 1) ≥ 0 := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have h5 : a (n + 2) ^ 3 = 99 * (a (n + 1)) ^ 3 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      have h6 : a (n + 2) ^ 3 ≥ 0 := by
        have h7 : a (n + 1) ≥ 0 := ih
        have h8 : (a (n + 1)) ^ 3 ≥ 0 := by
          apply pow_nonneg
          linarith
        nlinarith [h5, show (99 : ℝ) > 0 by norm_num]
      have h2 : a (n + 2) ≥ 0 := by
        by_contra h
        push_neg at h
        have h3 : a (n + 2) ^ 3 < 0 := by
          have : a (n + 2) < 0 := by linarith
          nlinarith [sq_pos_of_neg this, sq_nonneg (a (n + 2)), sq_nonneg (a (n + 2) + 0)]
        nlinarith [h6, h3]
      linarith
  have h1 : a 100 ≥ 0 := by
    have h5' : ∀ (n : ℕ), a (n + 1) ≥ 0 := h5
    specialize h5' 99
    linarith
  have h7 : a 100 = (99 : ℝ) ^ 33 := by
    have h8 : a 100 ^ 3 - ( (99 : ℝ) ^ 99 ) = 0 := by
      nlinarith [h4]
    have h11 : a 100 ≥ 0 := h1
    have h10 : a 100 - (99 ^ 33) = 0 := by
      have h11 : a 100 ^ 3 - ( (99 : ℝ) ^ 99 ) = 0 := h8
      have h12 : a 100 ^ 3 - ( (99 : ℝ) ^ 99 ) = (a 100 - (99 ^ 33)) * (a 100 ^ 2 + (99 ^ 33) * a 100 + ((99 ^ 33) ^ 2)) := by
        ring_nf
      rw [h12] at h11
      cases' (mul_eq_zero.mp h11) with h13 h14
      · -- $a_100 - (99^33) = 0$
        linarith
      · -- $a_100 ^ 2 + (99 ^ 33) * a_100 + (99 ^ 33) ^ 2 = 0$
        nlinarith [sq_nonneg (a 100 + (99 ^ 33) / 2), sq_nonneg (a 100 + (99 ^ 33)), sq_nonneg (a 100 - (- (99 ^ 33))), sq_nonneg ((99 : ℝ) ^ 33), sq_nonneg (a 100 - (99 ^ 33)), sq_nonneg (a 100 ^ 2 - (99 ^ 33)), sq_nonneg ((99 : ℝ) ^ 33 * (99 : ℝ) ^ 33), sq_nonneg ((99 : ℝ) - (99 : ℝ) ) ]
    linarith
  norm_num at h7 ⊢
  linarith