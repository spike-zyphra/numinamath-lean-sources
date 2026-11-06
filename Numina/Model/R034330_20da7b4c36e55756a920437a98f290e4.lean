import Mathlib
theorem algebra_610636 (NF NC BF BC : ℝ) (hN : NF = 1.8 * NC + 32) (hB : BF = 1.8 * BC + 32) (h : NC = 10 + BC): NF = BF + 18:= by
  rw [hN, hB]
  rw [show NC = 10 + BC by linarith]
  ring_nf