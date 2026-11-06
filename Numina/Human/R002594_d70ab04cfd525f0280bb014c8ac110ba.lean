import Mathlib

open Real 
open Complex

/- Let $w$ and $z$ be complex numbers such that $|w| = 1$ and $|z| = 10$. 
Let $\theta = \arg \left(\tfrac{w-z}{z}\right)$. 
The maximum possible value of $\tan^2 \theta$ can be written as $\tfrac{p}{q}$, where $p$ and $q$ are relatively prime positive integers. 
Find $p+q$. 
(Note that $\arg(w)$, for $w \neq 0$, denotes the measure of the angle that the ray from $0$ to $w$ makes with the positive real axis in the complex plane) -/
theorem algebra_95945 (p q : ℕ) (hp_pos : p > 0) (hq_pos : q > 0) (hcop : p.Coprime q) 
(hpq : IsGreatest {x : ℝ | ∃ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 10 ∧ x = (Real.tan (Complex.arg ((w - z) / z))) ^ 2} ((p : ℝ) / q)) : p + q = 100 := by
  --for any pair of complex numbers w and z of norm 1 and 10 respectively, one can write tan((w - z)/z).arg)^2 = sin(w.arg-z.arg)^2/(cos(w.arg-z.arg)-10)^2
  have eq_gon2 : ∀ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 10 → (Real.tan ((w - z) / z).arg) ^ 2 = Real.sin (Complex.arg w - Complex.arg z) ^ 2 / (Real.cos (Complex.arg w - Complex.arg z) - 10) ^ 2 := by 
    --first notice that (w - z)/z = 1/10 * cos(w.arg-z.arg) + 1/10 * sin(w.arg-z.arg)*i - 1 by trigonometric equalities involving rewriting the complex numbers in exponential and polar notations.
    have eq_gon1 : ∀ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 10 → (w - z) / z = (1 : ℝ) / 10 * Real.cos (Complex.arg w - Complex.arg z) + (1 : ℝ) / 10 * Real.sin (Complex.arg w - Complex.arg z) * .I - 1 := by
      rintro w z ⟨hw, hz⟩
      rw[Complex.norm_eq_abs] at hw hz
      rw[(by rw[← sub_mul, mul_div_mul_comm, div_self (by apply ne_zero_of_norm_ne_zero; rw[Complex.norm_eq_abs, abs_conj, hz]; linarith), mul_one]; : (w - z) / z = (w * (starRingEnd ℂ) z - z * (starRingEnd ℂ) z) / (z * (starRingEnd ℂ) z))]
      repeat rw[Complex.mul_conj, Complex.normSq_eq_abs, hz, sub_div]
      simp
      nth_rw 1 [← Complex.abs_mul_exp_arg_mul_I w, ← Complex.abs_mul_exp_arg_mul_I ((starRingEnd ℂ) z)]
      rw[Complex.abs_conj, mul_assoc, mul_comm ((Complex.abs z) : ℂ), ← mul_assoc (cexp (↑w.arg * I))]
      rw[← Complex.exp_add, (by ring_nf : (w.arg : ℂ) * I + (((starRingEnd ℂ) z).arg : ℂ) * I = ((w.arg : ℂ) + (((starRingEnd ℂ) z).arg : ℂ)) * I), ← Complex.cos_add_sin_I]
      rw[hw, hz]
      field_simp
      ring_nf
      rw[Complex.arg_conj]
      --we have to divide the cases when z is real and not real
      by_cases h : z.arg = π
      · simp[h]
        rw[← Complex.sin_add_two_pi ((w.arg : ℂ) - (π : ℂ)), ← Complex.cos_add_two_pi ((w.arg : ℂ) - (π : ℂ)) ]
        ring_nf
      · simp[h]
        ring_nf
    rintro w z ⟨hw, hz⟩ 
    rw[eq_gon1]
    simp
    norm_cast
    simp
    rw[← div_pow, sq_eq_sq_iff_eq_or_eq_neg]
    left
    field_simp
    constructor
    · exact hw
    · exact hz
  --prove that 1/99 is in fact the largest number satisfying all the properties
  have hIsG199 : IsGreatest {x : ℝ | ∃ w z : ℂ, ‖w‖ = 1 ∧ ‖z‖ = 10 ∧ x = (Real.tan (Complex.arg ((w - z) / z))) ^ 2} ((1 : ℝ) / 99) := by
    unfold IsGreatest
    constructor
    --first it has all the properties
    · simp
      simp at eq_gon2
      --we can find two complex numbers of norm 1 and 10 so that the difference of the args is arccos(1/10)
      use (cexp (Real.arccos (1 / 10) * Complex.I))
      rw[Complex.abs_eq_one_iff]
      constructor
      · use (arccos (1 / 10))
      · use 10
        constructor
        · simp
        · simp
          rw[Real.cos_arccos (by field_simp; linarith) (by norm_num), div_pow, div_pow, Real.sin_sq, Real.cos_arccos (by field_simp; linarith) (by norm_num)]
          ring_nf
    --it is the upperbound, this can be seen by developing algebraically the inequality
    · unfold upperBounds
      simp
      intro a w hw z hz ainset
      specialize eq_gon2 w z (by constructor; exact hw; exact hz)
      simp at eq_gon2
      rw[eq_gon2] at  ainset
      have cos10neg : Real.cos (w.arg - z.arg) - 10 < 0  := by
        norm_num
        exact lt_of_lt_of_le' (by linarith) (Real.cos_le_one (w.arg - z.arg))
      rw[ainset, div_le_iff₀ (sq_pos_of_neg cos10neg), Real.sin_sq]
      field_simp
      rw[le_div_iff₀ (by linarith)]
      norm_num
      rw[sub_sq, ← add_le_add_iff_left (-99)]
      ring_nf
      rw[(by ring_nf : 1 - Real.cos (w.arg - z.arg) * 20 + Real.cos (w.arg - z.arg) ^ 2 * 100 = (10 * Real.cos (w.arg - z.arg) - 1) ^ 2)]
      --one ends up with the condition that a perfect square must be non-negative, which is always the case
      by_cases k : (10 * Real.cos (w.arg - z.arg) - 1) > 0
      · exact le_of_lt (sq_pos_of_pos k)
      · by_cases k' : (10 * Real.cos (w.arg - z.arg) - 1) = 0
        rw[k']
        linarith
        · have k'' : (10 * Real.cos (w.arg - z.arg) - 1) < 0 := by
            by_contra l
            push_neg at k k' l
            have eeq : 10 * Real.cos (w.arg - z.arg) - 1 = 0 := by linarith
            rw[eeq] at k'
            contradiction
          exact le_of_lt (sq_pos_of_neg k'')
  --now that we know that 1/99 fulfills the dsired properties we can say that the upper bound is unique, hence p/q is 1/99
  have heq' : (p : ℝ) / q = (1 : ℝ) / 99 := by exact IsGreatest.unique hpq hIsG199
  field_simp at heq'
  norm_cast at heq'
  rw[← heq']
  ring_nf
  --since p and q are coprime and p ∣ q, this forces p = 1, q = 999 and we have the desired result p+q=100
  have hp_one : p = 1 := by exact Nat.eq_one_of_dvd_coprimes hcop (by rfl) (by rw[dvd_iff_exists_eq_mul_right]; use 99; symm; exact heq') 
  rw[hp_one]
  ring_nf