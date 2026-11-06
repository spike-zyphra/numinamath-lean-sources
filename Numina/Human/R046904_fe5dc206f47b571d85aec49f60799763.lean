import Mathlib

open Real Set
open scoped Real

/- Example 7 Given $x \in\left(0, \frac{\pi}{2}\right)$,
try to find the maximum value of the function $f(x)=3 \cos x + 4 \sqrt{1+\sin ^{2} x}$,
and the corresponding $x$ value. -/

theorem algebra_599852:
  IsGreatest {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = 3 * cos x + 4 * sqrt (1 + sin x ^ 2)} (5 * sqrt 2) := by

  -- we prove cauchy_inequality for n = 2 case firstly
  have cauchy_ineq: ∀ a b c d: ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
  (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    intro a b c d h
    rcases h with ⟨ha, hb, hc, hd⟩
    have ineq: 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 := by
      rw [show (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2
       = (a * d - b * c) ^ 2 by ring]
      apply sq_nonneg
    nlinarith

  constructor
  -- the forward direction: show that it's achievable
  .
    simp only [Set.mem_setOf_eq]
    use arccos (3 / 5 * √2)
    constructor
    .
      simp
      rw [show 3 / 5 * √2 = 3 * √2 / 5 by ring]
      rw [div_lt_one]
      .
        rw [← sq_lt_sq₀]
        rw [show (3 * √2) ^ 2 = 9 * √2 ^ 2 by ring]
        rw [show √2 ^ 2 = 2 by norm_num]
        norm_num
        have o:= sqrt_nonneg 2
        nlinarith
        norm_num
      .
        norm_num
    .
      rw [Real.cos_arccos]
      rw [Real.sin_arccos]
      rw [show (3 / 5 * √2) ^ 2 = 9 / 25 * √2 ^ 2 by ring]
      rw [show √2 ^ 2 = 2 by norm_num]
      norm_num
      rw [show (√7 / √25) ^ 2 = √7 ^ 2 / √25 ^ 2 by ring]
      rw [Real.sq_sqrt]
      rw [Real.sq_sqrt]
      rw [show (1: ℝ) + 7 / 25 = 32 / 25 by norm_num]
      rw [Real.sqrt_div]
      have s1: √32 = 4 * √2 := by
        rw [← sq_eq_sq₀]
        rw [Real.sq_sqrt]
        ring_nf
        rw [Real.sq_sqrt]
        all_goals norm_num
      have s2: √25 = 5 := by
        rw [← sq_eq_sq₀]
        rw [Real.sq_sqrt]
        all_goals norm_num
      rw [s1,s2]
      ring
      all_goals norm_num
      . have o: 0 ≤ √2 := by apply Real.sqrt_nonneg
        nlinarith
      . rw [show 3 / 5 * √2 = 3 * √2 / 5 by ring]
        rw [div_le_one]
        rw [← sq_le_sq₀]
        rw [show (3 * √2) ^ 2 = 9 * √2 ^ 2 by ring]
        rw [show √2 ^ 2 = 2 by norm_num]
        norm_num
        have o:= sqrt_nonneg 2
        nlinarith
        norm_num
        norm_num


  -- the backward direction
  .
    intro y h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨x, hx, h⟩ := h
    replace hx: 0 < cos x := by
      apply Real.cos_pos_of_mem_Ioo
      simp at *
      rcases hx with ⟨l1, l2⟩
      constructor
      .
        nlinarith [Real.pi_gt_d2]
      .
        nlinarith [Real.pi_gt_d2]
    have hy: y ^ 2 ≤ 50 := by
      rw [h]  -- we use cauchy_ineq to prove this
      specialize cauchy_ineq 3 4 (cos x) (sqrt (1 + sin x ^ 2))
      norm_num at cauchy_ineq
      simp [hx] at cauchy_ineq
      have o: 0 < 1 + sin x ^ 2 := by
        nlinarith
      simp [o] at cauchy_ineq
      have eq: cos x ^ 2 + √(1 + sin x ^ 2) ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        have r:= Real.cos_sq_add_sin_sq x
        nlinarith
        linarith
      rw [eq] at cauchy_ineq
      norm_num at cauchy_ineq
      exact cauchy_ineq
    have o: 50 = (5 * √2) ^ 2 := by
      ring_nf
      rw [show √2 ^ 2 = 2 by norm_num]
      norm_num
    rw [o] at hy
    rw [sq_le_sq₀] at hy
    exact hy
    have i: 0 ≤ √(1 + sin x ^ 2) := by
      apply Real.sqrt_nonneg
    nlinarith
    have j:= Real.sqrt_nonneg 2
    nlinarith