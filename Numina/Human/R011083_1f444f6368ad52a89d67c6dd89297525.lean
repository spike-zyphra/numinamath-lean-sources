import Mathlib

-- a lemma for factoring
lemma lemma_1 (x: ℝ): x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = (x ^ 3 + 1) * (x ^ 2 + x + 1) := by
    ring

-- an inequality lemma derived from AM-GM
lemma lemma_2 (x: ℝ) (hx: 0 < x): 2 * √(x ^ 3) ≤ x ^ 3 + 1 := by
  set y:= x ^ 3
  have o: 0 ≤ y := by
    simp [y]
    have r1: 0 ≤ x ^ 2 := by
      nlinarith
    rw [show x ^ 3 = x * x ^ 2 by ring]
    nlinarith
  have eq: y = √y ^ 2 := by
    rw [← Real.sqrt_eq_iff_eq_sq]
    exact o
    apply Real.sqrt_nonneg
  nth_rewrite 2 [eq]
  clear eq
  set s:= √y
  clear_value s
  have u: 0 ≤ s ^ 2 + 1 - 2 * s := by
    rw [show s ^ 2 + 1 - 2 * s = (s - 1) ^ 2 by ring]
    apply sq_nonneg
  nlinarith

/-Let a b c be positive real numbers such that abc = 1. Prove that
(a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) *
    (c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1) ≥ 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)-/

theorem inequalities_108074 {a b c: ℝ} (h: a * b * c = 1) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c):
    (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) *
    (c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1) ≥ 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by

  have fa:= lemma_1 a
  have fb:= lemma_1 b
  have fc:= lemma_1 c

  -- use lemma to simplify
  rw [fa, fb, fc]
  clear fa fb fc
  rw [show (a ^ 3 + 1) * (a ^ 2 + a + 1) * ((b ^ 3 + 1) * (b ^ 2 + b + 1)) * ((c ^ 3 + 1) * (c ^ 2 + c + 1))
  = ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) * ((a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1)) by ring]
  rw [show 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) =
  8 * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) by ring]

  -- take out the same term on both sides
  set S:= (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)

  -- show the final inequality
  have l: 8 ≤ (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) := by
    have la:= lemma_2 a ha
    have lb:= lemma_2 b hb
    have lc:= lemma_2 c hc
    have eq: √(a ^ 3) * √(b ^ 3) * √(c ^ 3) = 1 := by
      rw [← Real.sqrt_mul]
      rw [← Real.sqrt_mul]
      rw [show a ^ 3 * b ^ 3 * c ^ 3 = (a * b * c) ^ 3 by ring]
      simp [h]
      have ra: 0 ≤ a ^ 3 := by
        have r1: 0 ≤ a ^ 2 := by
          nlinarith
        rw [show a ^ 3 = a * a ^ 2 by ring]
        nlinarith
      have rb: 0 ≤ b ^ 3 := by
        have r1: 0 ≤ b ^ 2 := by
          nlinarith
        rw [show b ^ 3 = b * b ^ 2 by ring]
        nlinarith
      apply mul_nonneg
      exact ra
      exact rb
      have r1: 0 ≤ a ^ 2 := by
          nlinarith
      rw [show a ^ 3 = a * a ^ 2 by ring]
      nlinarith
    have y1: 0 ≤ 2 * √(b ^ 3) * (2 * √(c ^ 3)) := by
      have r1: 0 ≤ √(b ^ 3) := by
        apply Real.sqrt_nonneg
      have r2: 0 ≤ √(c ^ 3) := by
        apply Real.sqrt_nonneg
      nlinarith
    have y2: 0 ≤ 2 * √(c ^ 3) := by
      have r1: 0 ≤ √(c ^ 3) := by
        apply Real.sqrt_nonneg
      nlinarith
    have y3: 0 ≤ (a ^ 3 + 1) * (b ^ 3 + 1) := by
      have t1: 0 ≤ a ^ 3 + 1 := by
        nlinarith
      have t2: 0 ≤ b ^ 3 + 1 := by
        have p: 0 ≤ b ^ 3 := by
          have r1: 0 ≤ b ^ 2 := by
            nlinarith
          rw [show b ^ 3 = b * b ^ 2 by ring]
          nlinarith
        nlinarith
      nlinarith
    calc
      8 = 8 * (√(a ^ 3) * √(b ^ 3) * √(c ^ 3)) := by rw [eq]; simp
      _ = (2 * √(a ^ 3)) * ((2 * √(b ^ 3)) * (2 * √(c ^ 3))) := by ring
      _ ≤ (a ^ 3 + 1) * ((2 * √(b ^ 3)) * (2 * √(c ^ 3))) := by apply mul_le_mul_of_nonneg_right; exact la; exact y1
      _ ≤ (a ^ 3 + 1) * ((b ^ 3 + 1) * (2 * √(c ^ 3))) := by apply mul_le_mul_of_nonneg_left; apply mul_le_mul_of_nonneg_right; exact lb; exact y2; nlinarith
      _ = ((a ^ 3 + 1) * (b ^ 3 + 1)) * (2 * √(c ^ 3)) := by ring
      _ ≤ (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) := by apply mul_le_mul_of_nonneg_left; exact lc; exact y3

  -- finally, derive the inequality
  simp
  rw [show 8 * S = S * 8 by ring]
  apply mul_le_mul_of_nonneg_left
  exact l
  have r1: 0 ≤ a ^ 2 + a + 1 := by
    nlinarith
  have r2: 0 ≤ (a ^ 2 + a + 1) * (b ^ 2 + b + 1) := by
    nlinarith
  simp [S]
  nlinarith