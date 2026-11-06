import Mathlib

-- we first show a simp inequality which will be used many times
lemma lemma_1 (x y: ℝ) (h: x ≠ y): 2 * (x ^ 2 + y ^ 2) > (x + y) ^ 2 := by

  suffices 0 < 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2 by
    linarith
  rw [show 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2 = (x - y) ^ 2 by ring]
  suffices 0 ≤ (x - y) ^ 2 ∧ (x - y) ^ 2 ≠ 0 by
    set p:= (x - y) ^ 2
    clear_value p
    by_contra! f
    replace f: p = 0 := by linarith
    simp [f] at this
  constructor
  .
    nlinarith
  .
    by_contra! o
    simp at o
    replace o: x = y := by linarith
    simp [o] at h

-- then we show the key local inequality
lemma lemma_2 (x y: ℝ) (hx: 0 < x) (hy: 0 < y) (h: x ≠ y): (x ^ 4 + y ^ 4) / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) > (x + y) / 4 := by
  rw [show x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 = (x ^ 2 + y ^ 2) * (x + y) by ring]
  have f1:= lemma_1 (x^2) (y^2)
  have o: x ^ 2 ≠ y ^ 2 := by
    by_contra! o
    replace o: (x - y) * (x + y) = 0 := by
      nlinarith
    simp at o
    rcases o with o | o
    .
      replace o: x = y := by linarith
      simp [o] at h
    .
      linarith
  simp [o] at f1
  rw [show (x ^ 2) ^ 2 = x ^ 4 by ring] at f1
  rw [show (y ^ 2) ^ 2 = y ^ 4 by ring] at f1
  rw [gt_iff_lt]
  rw [div_lt_div_iff₀]
  suffices (x + y) * ((x ^ 2 + y ^ 2) * (x + y)) < 2 * (x ^ 2 + y ^ 2) ^ 2 by
    nlinarith
  have f2:= lemma_1 x y (by tauto)
  simp at f2
  clear f1
  nlinarith
  norm_num
  positivity

-- use lemma_2 to derive the general version
lemma lemma_3 (x y: ℝ) (hx: 0 < x) (hy: 0 < y): (x ^ 4 + y ^ 4) / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) ≥ (x + y) / 4 := by
  by_cases r: x ≠ y

  -- case x ≠ y, we use lemma_2 directly
  .
    have f1:= lemma_2 x y (by tauto) (by tauto) (by tauto)
    linarith

  -- case x = y
  .
    simp at r
    simp [r]
    ring_nf
    field_simp
    rw [div_le_div_iff₀]
    nlinarith
    norm_num
    positivity

/-Exercise 9. Let a,b,c,d be strictly positive real numbers such that:
a+b+c+d=1. Show that:
a^4 / (a^3 + a^2 * b + a * b^2 + b^3) + b^4 / (b^3 + b^2 * c + b * c^2 + c^3) + c^4 / (c^3 + c^2 * d + c * d^2 + d^3) + d^4 / (d^3 + d^2 * a + d * a^2 + a^3) ≥ 1/4.
and determine the cases of equality.-/

theorem inequalities_294107 (a b c d: ℝ) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (hd: 0 < d) (h: a + b + c + d = 1):
  a^4 / (a^3 + a^2 * b + a * b^2 + b^3) + b^4 / (b^3 + b^2 * c + b * c^2 + c^3) +
  c^4 / (c^3 + c^2 * d + c * d^2 + d^3) + d^4 / (d^3 + d^2 * a + d * a^2 + a^3) ≥ 1/4 ∧
  (a^4 / (a^3 + a^2 * b + a * b^2 + b^3) + b^4 / (b^3 + b^2 * c + b * c^2 + c^3) +
  c^4 / (c^3 + c^2 * d + c * d^2 + d^3) + d^4 / (d^3 + d^2 * a + d * a^2 + a^3) = 1/4 ↔
  a = 1 / 4 ∧ b = 1 / 4 ∧ c = 1 / 4 ∧ d = 1 / 4) := by

  -- we write the left side by S
  set S:= a^4 / (a^3 + a^2 * b + a * b^2 + b^3) + b^4 / (b^3 + b^2 * c + b * c^2 + c^3) +
  c^4 / (c^3 + c^2 * d + c * d^2 + d^3) + d^4 / (d^3 + d^2 * a + d * a^2 + a^3)

  set S':= b^4 / (a^3 + a^2 * b + a * b^2 + b^3) + c^4 / (b^3 + b^2 * c + b * c^2 + c^3) +
  d^4 / (c^3 + c^2 * d + c * d^2 + d^3) + a^4 / (d^3 + d^2 * a + d * a^2 + a^3)

  set T:= (a^4 + b^4) / (a^3 + a^2 * b + a * b^2 + b^3) + (b^4 + c^4) / (b^3 + b^2 * c + b * c^2 + c^3) +
  (c^4 + d^4) / (c^3 + c^2 * d + c * d^2 + d^3) + (d^4 + a^4) / (d^3 + d^2 * a + d * a^2 + a^3)

  -- then we show that S is indeed half of T
  have u: S = T / 2 := by
    have o1: T = S + S' := by
      simp [T, S, S']
      set p:= a^3 + a^2 * b + a * b^2 + b^3
      set q:= b^3 + b^2 * c + b * c^2 + c^3
      set r:= c^3 + c^2 * d + c * d^2 + d^3
      set s:= d^3 + d^2 * a + d * a^2 + a^3
      clear_value S S' T p q r s
      repeat rw [add_div]
      ring
    have o2: S = S' := by
      clear_value T
      suffices S - S' = 0 by
        clear *- this
        clear_value S S'
        linarith
      simp [S, S']
      field_simp
      ring
    clear *- o1 o2
    clear_value S S' T
    linarith
  rw [u]
  clear u
  clear_value S S'

  have f1:= lemma_3 a b (by tauto) (by tauto)
  have f2:= lemma_3 b c (by tauto) (by tauto)
  have f3:= lemma_3 c d (by tauto) (by tauto)
  have f4:= lemma_3 d a (by tauto) (by tauto)
  constructor

  -- show the inequality
  .
    suffices T ≥ 1 / 2 by
      clear_value T
      clear *- this
      linarith
    simp [T]
    set p:= (a ^ 4 + b ^ 4) / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
    set q:= (b ^ 4 + c ^ 4) / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3)
    set r:= (c ^ 4 + d ^ 4) / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3)
    set s:= (d ^ 4 + a ^ 4) / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3)
    clear_value p q r s T
    suffices (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 ≤ p + q + r + s by
      suffices g: (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 = 1 / 2 by
        rw [g] at this
        rw [show 2⁻¹ = (1: ℝ) / 2 by simp]
        tauto
      clear *- h
      field_simp
      linarith
    nlinarith

  -- show the condition for equality
  .
    constructor

    -- the forward direction
    .
      intro g
      suffices a = b ∧ b = c ∧ c = d by
        clear *- this h
        simp [this] at h
        replace h: d = 1 / 4 := by linarith
        simp [h] at this
        rcases this with ⟨p, q, r⟩
        simp [r] at q
        simp [q] at p
        simp [p, q, r, h]
      by_contra! o
      suffices T > 1 / 2 by
        clear *- g this
        clear_value T
        nlinarith
      replace o: a ≠ b ∨ b ≠ c ∨ c ≠ d := by
        clear *- o
        tauto
      rcases o with o | o | o

      -- case a ≠ b
      .
        replace f1:= lemma_2 a b (by tauto) (by tauto) (by tauto)
        simp [T]
        set p:= (a ^ 4 + b ^ 4) / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
        set q:= (b ^ 4 + c ^ 4) / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3)
        set r:= (c ^ 4 + d ^ 4) / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3)
        set s:= (d ^ 4 + a ^ 4) / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3)
        clear_value p q r s T
        suffices (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 < p + q + r + s by
          suffices g: (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 = 1 / 2 by
            rw [g] at this
            rw [show 2⁻¹ = (1: ℝ) / 2 by simp]
            tauto
          clear *- h
          field_simp
          linarith
        nlinarith

      -- case b ≠ c
      .
        replace f2:= lemma_2 b c (by tauto) (by tauto) (by tauto)
        simp [T]
        set p:= (a ^ 4 + b ^ 4) / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
        set q:= (b ^ 4 + c ^ 4) / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3)
        set r:= (c ^ 4 + d ^ 4) / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3)
        set s:= (d ^ 4 + a ^ 4) / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3)
        clear_value p q r s T
        suffices (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 < p + q + r + s by
          suffices g: (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 = 1 / 2 by
            rw [g] at this
            rw [show 2⁻¹ = (1: ℝ) / 2 by simp]
            tauto
          clear *- h
          field_simp
          linarith
        nlinarith

      -- case c ≠ d
      .
        replace f3:= lemma_2 c d (by tauto) (by tauto) (by tauto)
        simp [T]
        set p:= (a ^ 4 + b ^ 4) / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
        set q:= (b ^ 4 + c ^ 4) / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3)
        set r:= (c ^ 4 + d ^ 4) / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3)
        set s:= (d ^ 4 + a ^ 4) / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3)
        clear_value p q r s T
        suffices (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 < p + q + r + s by
          suffices g: (a + b) / 4 + (b + c) / 4 + (c + d) / 4 + (d + a) / 4 = 1 / 2 by
            rw [g] at this
            rw [show 2⁻¹ = (1: ℝ) / 2 by simp]
            tauto
          clear *- h
          field_simp
          linarith
        nlinarith


    -- the backward direction
    .
      intro h
      simp [T, h]
      norm_num
