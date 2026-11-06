import Mathlib

open Complex
open scoped ComplexConjugate

/- 5. Let the complex numbers $z_{1}, z_{2}$ satisfy $\left|z_{1}\right|=\left|z_{1}+z_{2}\right|=3,\left|z_{1}-z_{2}\right|=3 \sqrt{3}$, then $\log _{3}\left|\left(z_{1} \overline{z_{2}}\right)^{2000}+\left(\overline{z_{1}} z_{2}\right)^{2000}\right|=$ -/

-- define Omega = 3rd root of unity
noncomputable
def Omega : ℂ := - 1 / 2 + √3 / 2 * I

-- √3^2 = 3 in complex numbers, used severa time
lemma l_sqrt_three_complex_sq : √3 ^ 2 = (3 : ℂ) := by
    norm_cast
    simp

-- Omega ^ 2's value
lemma l_Omega_sq : Omega ^ 2 = - 1 / 2 - √3 / 2 * I := by
  simp [Omega]
  ring_nf
  rw [l_sqrt_three_complex_sq]
  simp
  ring

-- Omega^2 is conjugate of Omega
lemma l_Omega_conj : conj Omega = Omega ^ 2 := by
  rw [l_Omega_sq]
  simp [Omega]
  rw [show (2 : ℂ) = ↑(2 : ℝ) by norm_cast, Complex.conj_ofReal]
  norm_cast

-- Omega^3 = 1
lemma l_Omega_pow_three : Omega ^ 3 = 1 := by
  rw [pow_succ, l_Omega_sq]
  simp [Omega]
  ring_nf
  rw [l_sqrt_three_complex_sq]
  simp
  norm_num

-- Omega ^ n can be converted to power modulo 3
lemma l_Omega_pow (n : ℕ) : Omega ^ n = Omega ^ (n % 3) := by
  nth_rw 1 [← Nat.mod_add_div n 3]
  ring_nf
  rw [mul_comm (n/3), pow_mul, l_Omega_pow_three]
  simp

-- Omega + Omega^2 = -1
lemma l_Omega_add_Omega_sq : Omega + Omega^2 = -1 := by
  rw [l_Omega_sq]
  simp [Omega]

theorem algebra_178584 (z1 z2 : ℂ) (h₀ : ‖z1‖ = 3) (h₁ : ‖z1 + z2‖ = 3)
    (h₂ : ‖z1 - z2‖ = 3 * Real.sqrt 3) :
    Real.logb 3 (‖(z1 * conj z2) ^ 2000 + (z2 * conj z1) ^ 2000‖) = 4000 := by
  -- apply square to h₁ h₂
  replace h₁ := congrArg (fun (x : ℝ) ↦ (x : ℂ)^2) h₁
  replace h₂ := congrArg (fun (x : ℝ) ↦ (x : ℂ)^2) h₂
  simp only at h₁ h₂
  -- write square as self * conj(self), then multiply and convert expressions to ‖z1‖^2 + ‖z2‖^2 +/--/ 2 * (z1 * conj z2).re
  rw [← Complex.mul_conj'] at h₁ h₂
  simp at h₁ h₂
  rw [show (3 * √3 : ℂ)^2 = 27 by norm_cast; ring_nf; simp; norm_num] at h₂
  norm_num at h₁
  ring_nf at h₁ h₂
  convert_to ‖z1‖^2 + ‖z2‖^2 + ↑(2 * (z1 * conj z2).re) = (9 : ℂ) using 1 at h₁
  . rw [← Complex.mul_conj', ← Complex.mul_conj', ← add_conj]
    simp
    ring
  convert_to ‖z1‖^2 + ‖z2‖^2 - ↑(2 * (z1 * conj z2).re) = (27 : ℂ) using 1 at h₂
  . rw [← Complex.mul_conj', ← Complex.mul_conj', ← add_conj]
    simp
    ring
  -- so normsq of both added is 18
  have h₃ : ‖z1‖^2 + ‖z2‖^2 = (18 : ℂ) := by linear_combination h₁/2 + h₂/2
  rw [h₀] at h₃
  norm_cast at h₃
  push_cast at h₃
  replace h₃ : ‖z2‖^2 = 3^2 := by linarith
  rw [sq_eq_sq₀ (by exact norm_nonneg z2) (by norm_num)] at h₃
  -- the real part of z1 * conj z2 is -9/2
  have h₄ : (z1 * conj z2).re = (-9 / 2: ℂ) := by
    push_cast at h₁ h₂
    linear_combination h₁/4 - h₂/4
  replace h₄ : (z1 * conj z2).re = (-9 / 2) := by
    norm_cast at h₄ ⊢
  -- by ‖z1‖, ‖z2‖, we have ‖z1 * conj(z2)‖ = 9
  have h₅ : ‖z1 * conj z2‖ = 9 := by
    simp [h₀, h₃]
    norm_num
  -- one term in target is conj (z1 * conj (z2))
  have h₆ : z2 * conj z1 = conj (z1 * conj z2) := by simp; ring
  -- imaginarty part of z1 * conj(z2) square is 9 * √3/2 or - 9 * √3/2
  replace h₅ : (z1 * conj z2).im ^ 2 = (9 * √3 / 2)^2 := by
    have := normSq_apply (z1 * conj z2)
    rw [h₄, Complex.normSq_eq_abs] at this
    ring_nf at this
    convert_to (9 ^ 2 : ℝ) = _ at this
    . simp at h₅ ⊢
      rw [h₅]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith
  norm_cast at h₅
  replace h₅ := eq_or_eq_neg_of_sq_eq_sq _ _ h₅
  -- so z1 * conj z2 is 9 * Omega or 9 * Omega^2 (using real and imaginary parts)
  replace h₅ : z1 * conj z2 = 9 * Omega ∨ z1 * conj z2 = 9 * Omega ^ 2 := by
    obtain h₅ | h₅ := h₅
    . left
      apply Complex.ext
      . simp [h₄, Omega]; norm_num
      . simp [h₅, Omega]; ring
    . right
      apply Complex.ext
      . simp [h₄, l_Omega_sq]; norm_num
      . simp [h₅, l_Omega_sq]; ring
  -- then expression in target is 9 ^ 2000 * (Omeg^2000 + (Omega^2)^2000)
  have h₇ : (z1 * conj z2) ^ 2000 + (z2 * conj z1) ^ 2000 = 9 ^ 2000 * (Omega ^ 2000 + (Omega ^ 2) ^ 2000) := by
    rw [h₆]
    obtain h₅ | h₅ := h₅
    . rw [h₅]
      simp
      rw [show (9 : ℂ) = ↑(9 : ℝ) by norm_cast, Complex.conj_ofReal, l_Omega_conj]
      push_cast
      ring
    . rw [h₅]
      simp
      have : (Omega ^ 2) ^ 2 = Omega := by
        ring_nf
        rw [l_Omega_pow]
        norm_num
      rw [show (9 : ℂ) = ↑(9 : ℝ) by norm_cast, Complex.conj_ofReal, l_Omega_conj, this]
      push_cast
      ring
  -- we convert target to logb 3 ‖9 ^ n * -1‖ using Omega lemmas
  rw [h₇, ← pow_mul,l_Omega_pow, l_Omega_pow (2 * 2000), show 2000 % 3 = 2 by norm_num,
      show 2 * 2000 % 3 = 1 by norm_num, pow_one, add_comm, l_Omega_add_Omega_sq]
  -- we have to generalize 2000 as 9^2000 is too big for lean to handle, then goal is logb 3 9^n = 2 *n, proved easily
  rw [show (4000 : ℝ) = 2 * ↑(2000 : ℕ) by norm_num]
  generalize 2000 = n
  have : ‖(9 ^ n * -1 : ℂ)‖ = (9 ^ n : ℝ) := by
    norm_cast
    simp
  rw [this, show 9 = (3 : ℝ) ^ 2 by norm_num, ← pow_mul, ← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  norm_cast