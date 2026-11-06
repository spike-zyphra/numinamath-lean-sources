import Mathlib

-- Determine a four-digit number M such that when M is multiplied by 4, the resulting number N = 4 × M satisfies the following conditions: 1.N is also a four-digit number. 2.The digits of N are the reverse of the digits of M.
theorem number_theory_613045 (w x y z M N : ℕ)(hw : 1 ≤ w ∧ w ≤ 9)(hx : x ≤ 9)(hy : y ≤ 9)(hz : z ≤ 9)(hM : M = 1000 * w + 100 * x + 10 * y + z)(hN : N = 1000 * z + 100 * y + 10 * x + w)(hMN : N = 4 * M) : M = 2178 := by
  rw[hM, hN] at hMN
  ring_nf at hMN
  have h : w ≤ 2 := by omega
  by_cases hwone : w = 1
  · omega
  · omega
