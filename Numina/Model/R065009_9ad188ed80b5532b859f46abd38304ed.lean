import Mathlib

theorem algebra_316547 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (L M N : ℝ)
    (hL : L = 1 / ((a - b) * (a - c)))
    (hM : M = 1 / ((b - a) * (b - c)))
    (hN : N = 1 / ((c - a) * (c - b))) :
    a * L + b * M + c * N = 0 ∧
    a ^ 2 * L + b ^ 2 * M + c ^ 2 * N = 1 ∧
    a ^ 3 * L + b ^ 3 * M + c ^ 3 * N = a + b + c := by
  constructor
  · -- Proof of (1) a * L + b * M + c * N = 0
    rw [hL, hM, hN]
    field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
      (show b - a ≠ 0 by intro h; apply ha; linarith), 
      (show b - c ≠ 0 by intro h; apply hb; linarith), 
      (show c - b ≠ 0 by intro h; apply hb; linarith), 
      (show a - c ≠ 0 by intro h; apply hc; linarith), 
      (show c - a ≠ 0 by intro h; apply hc; linarith)]
    ring
  constructor
  · -- Proof of (2) a^2 * L + b^2 * M + c^2 * N = 1
    rw [hL, hM, hN]
    field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
      (show b - a ≠ 0 by intro h; apply ha; linarith), 
      (show b - c ≠ 0 by intro h; apply hb; linarith), 
      (show c - b ≠ 0 by intro h; apply hb; linarith), 
      (show a - c ≠ 0 by intro h; apply hc; linarith), 
      (show c - a ≠ 0 by intro h; apply hc; linarith)]
    ring_nf
    <;> field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
      (show b - a ≠ 0 by intro h; apply ha; linarith), 
      (show b - c ≠ 0 by intro h; apply hb; linarith), 
      (show c - b ≠ 0 by intro h; apply hb; linarith), 
      (show a - c ≠ 0 by intro h; apply hc; linarith), 
      (show c - a ≠ 0 by intro h; apply hc; linarith)]
    <;> ring
  · -- Proof of (3) a^3 * L + b^3 * M + c^3 * N = a + b + c
    rw [hL, hM, hN]
    field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
      (show b - a ≠ 0 by intro h; apply ha; linarith), 
      (show b - c ≠ 0 by intro h; apply hb; linarith), 
      (show c - b ≠ 0 by intro h; apply hb; linarith), 
      (show a - c ≠ 0 by intro h; apply hc; linarith), 
      (show c - a ≠ 0 by intro h; apply hc; linarith)]
    ring_nf
    <;> field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
      (show b - a ≠ 0 by intro h; apply ha; linarith), 
      (show b - c ≠ 0 by intro h; apply hb; linarith), 
      (show c - b ≠ 0 by intro h; apply hb; linarith), 
      (show a - c ≠ 0 by intro h; apply hc; linarith), 
      (show c - a ≠ 0 by intro h; apply hc; linarith)]
    <;> ring