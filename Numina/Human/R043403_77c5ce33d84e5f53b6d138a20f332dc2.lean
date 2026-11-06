import Mathlib

theorem number_theory_174374 (k : ℕ) :
    7 ∣ 2^(6*k + 1) + 3^(6*k + 1) + 5^(6*k) + 1 := by
  -- Proof by induction on k
  induction k with
  | zero =>
    -- Base case: k = 0. Then we have $2^{1}+3^{1}+5^{0}+1 = 2+3+1+1 = 7$ which is divisible by 7.
    norm_num
  | succ k ih =>
    -- Inductive step: Assume the formula holds for k, prove for k+1
    have h1 : 2^(6 * (k + 1) + 1) + 3^(6 * (k + 1) + 1) + 5^(6 * (k + 1)) + 1 =
      2^(6 * k + 1) * 2^6 + 3^(6 * k + 1) * 3^6 + 5^(6 * k) * 5^6 + 1 := by
        ring_nf
    rw [h1]
    -- Separate into two parts: the induction hypothesis and a multiple of 7
    have h2 : 2^(6 * k + 1) * 2^6 + 3^(6 * k + 1) * 3^6 + 5^(6 * k) * 5^6 + 1 =
      (2^(6 * k + 1) + 3^(6 * k + 1) + 5^(6 * k) + 1) + (2^(6 * k + 1) * 63 + 3^(6 * k + 1) * 728 + 5^(6 * k) * 15624) := by
        ring
    rw [h2]
    omega
