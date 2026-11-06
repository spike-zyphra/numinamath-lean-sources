import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_96883 {f : ℂ → ℂ} (hf : ∀ z, f z = I * (z.1 - I * z.2)) :
    {z | ‖z‖ = 5 ∧ f z = z}.ncard = 2 := by
  have h1 : {z | ‖z‖ = 5 ∧ f z = z} = {(5 * Real.sqrt 2 / 2 : ℝ) + (5 * Real.sqrt 2 / 2 : ℝ) * I, - (5 * Real.sqrt 2 / 2 : ℝ) - (5 * Real.sqrt 2 / 2 : ℝ) * I} := by
    ext z
    simp only [hf, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, we'll prove the forward implication: if z is in the intersection of {z | ‖z‖ = 5} and {z | f z = z}, then z must be one of the two complex solutions we found earlier.
      intro h
      rcases h with ⟨habs, heq⟩
      have h_eq_1 : z.re = z.im := by
        simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
          Complex.I_re, Complex.I_im] at heq ⊢
        <;> norm_num at heq ⊢
        <;> nlinarith
      have h_eq_2 : (z.re) ^ 2 + (z.im) ^ 2 = 25 := by
        have h1 : ‖z‖ = 5 := habs
        have h7 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
          simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
          <;> ring_nf
          <;> simp [Complex.normSq]
          <;> norm_num
          <;> all_goals ring_nf
          <;> norm_num
          <;> all_goals tauto
        rw [h7] at h1
        have h25 : (z.re ^ 2 + z.im ^ 2 : ℝ) = 25 := by
          calc
            (z.re ^ 2 + z.im ^ 2 : ℝ) = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; all_goals nlinarith [sq_nonneg (z.re), sq_nonneg (z.im), sq_nonneg (z.re ^ 2 + z.im ^ 2)]
            _ = (5) ^ 2 := by rw [h1]
            _ = (25 : ℝ) := by norm_num
        nlinarith
      rw [show z.im = z.re from by linarith [h_eq_1]] at h_eq_2
      have h_eq_3 : (z.re) ^ 2 = 25 / 2 := by
        nlinarith
      have h_eq_4 : z.re = Real.sqrt (25 / 2) ∨ z.re = - Real.sqrt (25 / 2) := by
        have h1 : (z.re) ^ 2 = 25 / 2 := h_eq_3
        have : (z.re - Real.sqrt (25 / 2)) * (z.re + Real.sqrt (25 / 2)) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (25 / 2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (25 / 2 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 this) with h2 h3
        · -- Case z.re = sqrt(25 / 2)
          left
          linarith
        · -- Case z.re = -sqrt(25 / 2)
          right
          linarith
      have h2 : Real.sqrt (25 / 2) = (5 * Real.sqrt 2) / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        all_goals nlinarith
      cases h_eq_4 with
      | inl h_eq_5 =>
        have h_eq_6 : z.re = (5 * Real.sqrt 2) / 2 := by
          rw [h2] at h_eq_5
          linarith
        have h_eq_7 : z.im = (5 * Real.sqrt 2) / 2 := by
          linarith [h_eq_1, h_eq_6]
        simp [Complex.ext_iff, h_eq_6, h_eq_7]
        <;> norm_num
        <;> ring_nf
        <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
        <;> ring_nf
        <;> norm_num
        all_goals ring_nf <;> norm_num
      | inr h_eq_5 =>
        have h_eq_6 : z.re = - (5 * Real.sqrt 2) / 2 := by
          have h_eq_neg : z.re = - Real.sqrt (25 / 2) := by
            tauto
          rw [h_eq_neg]
          rw [h2]
          <;> ring_nf
          <;> norm_num
          all_goals nlinarith
          all_goals tauto
        have h_eq_7 : z.im = - (5 * Real.sqrt 2) / 2 := by
          linarith [h_eq_1, h_eq_6]
        simp [Complex.ext_iff, h_eq_6, h_eq_7]
        <;> norm_num
        <;> ring_nf
        <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
        <;> ring_nf
        <;> norm_num
        all_goals ring_nf <;> norm_num
    · -- We'll now prove the reverse iimplication: both of these complex numbers satisfy our conditions.
      rintro (h_eq | h_eq)
      · -- First case: z = 5 * sqrt(2)/2 + 5 * sqrt(2)/2 * i
        rw [h_eq]
        constructor
        · -- Verify that |z| = 5
          have h7 : ‖( (5 * Real.sqrt 2 / 2 : ℝ) + (5 * Real.sqrt 2 / 2 : ℝ) * I )‖ = 5 := by
            simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf
            <;> norm_num
            <;> ring_nf
            <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
            all_goals norm_num
            all_goals nlinarith
          tauto
        · -- Verify that f z = z
          simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc, pow_two]
          all_goals norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
          <;> ring_nf
          <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
          all_goals ring_nf <;> norm_num
        <;> ring_nf
        <;> norm_num
        all_goals ring_nf
        all_goals norm_num
      · -- Second case: z = -5 * sqrt(2)/2 - 5 * sqrt(2)/2 * i
        rw [h_eq]
        constructor
        · -- Verify that |z| = 5
          have h7 : ‖(- (5 * Real.sqrt 2 / 2 : ℝ) - (5 * Real.sqrt 2 / 2 : ℝ) * I)‖ = 5 := by
            simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf
            <;> norm_num
            <;> ring_nf
            <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
            all_goals norm_num
            all_goals nlinarith
          tauto
        · -- Verify that f z = z
          simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc, pow_two]
          all_goals norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
          <;> ring_nf
          <;> norm_num [Real.sqrt_pos.mpr, Real.sqrt_nonneg, Real.sq_sqrt, pow_two]
          all_goals ring_nf <;> norm_num
          <;> ring_nf
          <;> norm_num
          all_goals ring_nf
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_pair (by
    -- Show that these two complex numbers are different
    intro h
    simp [Complex.ext_iff, mul_add, mul_assoc] at h
    <;> ring_nf at h
    <;> norm_num [Real.sqrt_pos.mpr, Real.sq_sqrt] at h
    <;> try { 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      }
  )]
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num