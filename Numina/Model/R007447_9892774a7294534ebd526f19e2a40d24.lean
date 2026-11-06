import Mathlib

theorem algebra_14711 (A B : ℝ) (hA : A = 8000) (hB : B = 10000)
    (hA' : A' = 0.06) (hB' : B' = 0.07) :
    round |A * (1 + A') ^ 20 - B * (1 + B' * 20)| = 1657 := by
  rw [hA, hB, hA', hB']
  norm_num [round_eq, abs]
  <;> try { norm_num }
  <;> try { linarith }