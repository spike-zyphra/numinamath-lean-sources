import Mathlib

namespace algebra_609755

noncomputable def z' : ℕ → ℂ
  | 0 => ↑(((4035:ℝ)^(1/1024:ℝ) - 1)/2)
  | (n+1) => 2 * (z' n)^2 + 2 * z' n

end algebra_609755

open algebra_609755

/- Given complex number $z$, define sequence $z_{0}, z_{1}, z_{2}, \ldots$ as
$z_{0}=z$ and $z_{n+1}=2 z_{n}^{2}+2 z_{n}$ for $n \geq 0$.
Given that $z_{10}=2017$, find the minimum possible value of $|z|$. -/
theorem algebra_609755:
  IsLeast {z0norm: ℝ| ∃(z: ℕ → ℂ), ‖z 0‖ = z0norm ∧ z 10 = 2017 ∧
    (∀n, z (n+1) = 2 * (z n)^2 + 2 * z n)} (((4035:ℝ)^(1/1024:ℝ) - 1)/2) := by
  -- given series z, we consider series w defined by wn = zn + 1/2.
  -- we can find its general formula by induction.
  have hw{z w: ℕ → ℂ}(hzsucc: ∀n, z (n+1) = 2 * (z n)^2 + 2 * z n)
    (w_def: ∀n, w n = z n + 1/2):
    ∀n, w n = 2^(2^n - 1) * (w 0)^(2^n) := by
    -- wn = zn + 1/2, so zn = wn - 1/2.
    have z_of_w(n:ℕ): z n = w n - 1/2 := by
      simp only [w_def n, add_sub_cancel_right]
    -- wn = zn + 1/2, by formula of z (n+1), we can prove that of w (n+1).
    have wsucc(n:ℕ): w (n+1) = 2 * (w n)^2 := by
      have h1: 2 * (z n)^2 + 2 * z n = 2 * (w n)^2 - 1/2 := by
        rw [z_of_w n]
        ring
      have h2 := hzsucc n
      rwa [z_of_w (n+1), h1, sub_left_inj] at h2
    intro n
    -- using indcution, we can find general formula of wn.
    induction' n with n ih
    · simp
    · rw [wsucc n, ih, mul_pow _ _ 2, ← mul_assoc]
      have h1: (2:ℂ)*(2^(2^n-1))^2 = 2^(2^(n+1)-1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        rw [pow_succ, Nat.sub_mul, one_mul]
        have: 2 ≤ 2^n * 2 := by
          have: 2^n ≥ 1 := Nat.one_le_two_pow
          omega
        omega
      have h2: ((w 0)^(2^n))^2 = (w 0)^(2^(n+1)) := by
        rw [← pow_mul]
        congr 1
      rw [h1, h2]
  -- therefore given z10 or w10, norm of w0 is determined.
  have w0norm{z w: ℕ → ℂ}(hzsucc: ∀n, z (n+1) = 2 * (z n)^2 + 2 * z n)
    (w_def: ∀n, w n = z n + 1/2)(hz10: z 10 = 2017):
    ‖w 0‖ = (4035:ℝ)^(1/1024:ℝ)/2 := by
    -- notice that z10 = 2017, then, w10 = 2017 - 1/2 = 4035/2
    have hw10: w 10 = 4035/2 := by
      rw [w_def 10, hz10]
      norm_num
    -- then (w0)^1024 2^1023 = 4035/2
    have hw0: (w 0)^1024 = 4035 / (2^1024) := by
      have h1: (w 0)^(2^10) = w 10 / (2^(2^10 - 1)) := by
        have := (hw hzsucc w_def) 10
        field_simp
        rw [this, mul_comm]
      have h2: 2^10 = 1024 := by norm_num
      rw [h2, hw10, div_div, ← pow_succ' (2:ℂ)] at h1
      simp only [Nat.add_one_sub_one, Nat.reduceAdd] at h1
      exact h1
    -- take norm for both sides.
    have: ‖(w 0)‖^1024 = ((4035:ℝ)^(1/1024:ℝ)/2)^1024 := by
      rw [← norm_pow, hw0]
      have h1: (4035:ℂ)/2^1024 = ↑((4035:ℝ)/(2^1024:ℝ)) := by simp
      rw [h1, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
      have h2: (4035:ℝ) = (4035^(1/1024:ℝ))^1024 := by
        rw [← Real.rpow_mul_natCast (by norm_num)]
        simp
      nth_rw 1 [h2, ← div_pow]
    -- thus norm w0 = 4035^(1/1024)/2
    apply (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp this
  -- and for the other direction, given z0, we can determine z10.
  have z10_of_z0{z w: ℕ → ℂ}(hzsucc: ∀n, z (n+1) = 2 * (z n)^2 + 2 * z n)
    (w_def: ∀n, w n = z n + 1/2)(hz0: z 0 = ↑(((4035:ℝ)^(1/1024:ℝ) - 1)/2)):
    z 10 = 2017 := by
    -- w0 = z0 + 1/2
    have hw0: w 0 = ↑((4035:ℝ)^(1/1024:ℝ)/2) := by
      rw [w_def 0, hz0]
      simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_ofNat, sub_div, sub_add_cancel]
    -- by general formula of w, w10 is determined.
    have hw10: w 10 = 4035/2 := by
      rw [(hw hzsucc w_def) 10]
      have h1: 2^10 = 1024 := by norm_num
      have h2: (w 0)^(2^10) = 4035 / 2^1024 := by
        rw [h1, hw0]
        norm_cast
        have: (1/1024:ℝ) * ↑(1024:ℕ) = 1 := by simp
        rw [div_pow, ← Real.rpow_mul_natCast (by norm_num), this, Real.rpow_one]
        simp only [Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_pow, Nat.cast_pow, Nat.cast_ofNat]
      have h3: (2:ℂ)^(2^10 - 1) = 2^1024 / 2 := by
        field_simp
        rw [h1, ← pow_succ]
      rw [h2, h3]
      field_simp
      ring
    -- therefore z10 also determined.
    rw [w_def] at hw10
    rw [eq_sub_of_add_eq hw10]
    norm_num
  -- thus almost done. back to the problem.
  rw [IsLeast, lowerBounds]
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  constructor
  · -- verify such series z exist.
    use z'
    have hz0: z' 0 = ↑(((4035:ℝ)^(1/1024:ℝ) - 1)/2) := rfl
    have hzsucc(n:ℕ): z' (n+1) = 2 * (z' n)^2 + 2 * z' n := rfl
    -- define wn = zn + 1/2
    let w: ℕ → ℂ := fun n => z' n + 1/2
    have w_def(n:ℕ): w n = z' n + 1/2 := rfl
    -- z10 is determined by calculation before.
    have := z10_of_z0 hzsucc w_def hz0
    refine ⟨?_, this, hzsucc⟩
    rw [hz0, Complex.norm_real, Real.norm_of_nonneg]
    apply div_nonneg ?_ (by norm_num)
    apply sub_nonneg.mpr
    apply Real.one_le_rpow (by norm_num) (by norm_num)
  · -- prove norm z0 ≤ 4035^(1/1024)/2 - 1/2 for any such z.
    intro z0norm z hz0 hz10 hzsucc
    -- define wn = zn + 1/2
    let w: ℕ → ℂ := fun n => z n + 1/2
    have w_def(n:ℕ): w n = z n + 1/2 := rfl
    -- by the calculation before, norm of z0 + 1/2 is determined.
    have h1 := w0norm hzsucc w_def hz10
    rw [w_def 0] at h1
    rw [← hz0]
    -- and obviously, ‖z0‖ ≥ ‖z0 + 1/2‖ - 1/2
    have h2: ‖z 0‖ ≥ ‖z 0 + 1/2‖ - 1/2 := by
      have hh1: ‖z 0‖ + ‖(1/2:ℂ)‖ ≥ ‖z 0 + 1/2‖ := norm_add_le _ _
      have hh2: ‖(1/2:ℂ)‖ = 1/2 := by
        have: (1/2:ℂ) = ↑(1/2:ℝ) := by simp
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
      rw [hh2] at hh1
      linarith [hh1]
    -- done.
    apply le_trans (le_of_eq ?_) h2
    rw [h1, sub_div]