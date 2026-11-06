import Mathlib

open Polynomial

/- Let P(x) = x^2 - 3x - 7 and let Q(x) and R(x) be two quadratic polynomials also with the coefficient of x^2 equal to 1. David computes each of the three sums P+Q, P+R, Q+R and is surprised to find that each pair of these sums has a common root, and these three common roots are distinct. If Q(0)=2, then R(0) = m/n, where m and n are relatively prime positive integers. Find m + n.
-/
theorem algebra_98221 {P Q R : Polynomial ℝ} (hP : P = X ^ 2 - 3 * X - 7)
(hQ : Q.degree = 2 ∧ Q.coeff 2 = 1) (hR : R.degree = 2 ∧ R.coeff 2 = 1)
(x y z : ℝ) (hdist: x ≠ y ∧ y ≠ z ∧ z ≠ x)
(hpq: (P+Q).eval x = 0 ∧ (P+Q).eval y = 0)
(hqr: (Q+R).eval y = 0 ∧ (Q+R).eval z = 0)
(hpr: (P+R).eval x = 0 ∧ (P+R).eval z = 0)
(hQ0 : Q.eval 0 = 2) (m n : ℕ) (hmn: m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ R.eval 0 = m / n)
: m + n = 71 := by
  -- first prove auxilary lemma that 2nd degree polynomials are expressed via 0th, 1st, 2nd coefficients
  have hP : P = X ^ 2 - C 3 * X - C 7 := by exact hP
  have hquad (A : Polynomial ℝ) (hdeg: A.degree = 2) : A = C (A.coeff 2) * X^2 + C (A.coeff 1) * X +  C (A.coeff 0) := by
    nth_rw 1 [as_sum_range_C_mul_X_pow A, natDegree_eq_of_degree_eq_some hdeg]
    simp [Finset.sum_range, Fin.sum_univ_three]
    ring
  -- next establish that R(0) = R.coeff 0
  obtain ⟨hm_pos, hn_pos, hmn_cop, hrmn⟩ := hmn
  rw [hquad R hR.left] at hrmn
  simp at hrmn
  -- Prove that Q.coeff 0 = 2 due to Q(0) = 2
  have hQ0' : Q.coeff 0 = 2 := by rw [hquad Q hQ.left] at hQ0; simp at hQ0; assumption
  -- now establish quadratic form for P+Q, Q+R, P+R
  have hpq' : P + Q = 2 * X^2 + C (Q.coeff 1 - 3) * X - C 7 + C 2 := by
    nth_rw 1 [hP, hquad Q hQ.left, hQ0', hQ.right]; simp; ring
  have hqr' : Q + R = 2 * X^2 + C (Q.coeff 1 + R.coeff 1) * X + C (R.coeff 0 + 2) := by
    nth_rw 1 [hquad Q hQ.left, hquad R hR.left, hQ0', hQ.right, hR.right]; simp; ring
  have hpr' : P + R = 2 * X^2 + C (R.coeff 1 - 3) * X + C (R.coeff 0 - 7) := by
    nth_rw 1 [hP, hquad R hR.left, hR.right]; simp; ring
  -- define a, b, c for Q and R's coefficients
  set a := Q.coeff 1
  set b := R.coeff 1
  set c := R.coeff 0
  -- prove that t being a root for the 3 polynomials mean an algebraic x^2 + kx + l = 0 equation
  have hpqt {t: ℝ} (h: (P+Q).eval t = 0) : t^2 + ((a-3)/2)*t + (-5/2) = 0 := by simp [hpq'] at h; linarith
  have hqrt {t: ℝ} (h: (Q+R).eval t = 0) : t^2 + ((a+b)/2)*t + ((c+2)/2) = 0 := by simp [hqr'] at h; linarith
  have hprt {t: ℝ} (h: (P+R).eval t = 0) : t^2 + ((b-3)/2)*t + ((c-7)/2) = 0 := by simp [hpr'] at h; linarith
  -- establish vieta's theorem for x^2 + kx + l = 0 with two distinct roots
  have hvieta {x y k l :ℝ} (h₁ : x^2 + k * x + l = 0) (h₂ : y^2 + k * y + l = 0) (h: x ≠ y) : x + y = -k ∧ x * y = l := by
    have : x - y ≠ 0 := by
      by_contra h'
      have : x = y := by linarith
      contradiction
    have h₃: (x^2 - y^2) + k * (x - y) = 0 := by linarith
    have h₄: (x-y) * (x + y + k) = 0 := by ring_nf; ring_nf at h₃; assumption
    simp at h₄
    obtain h' | h' := h₄
    . contradiction
    . have hg₁ : x + y = -k := by linarith
      have : -(x+y) = k := by linarith
      rw [← this] at h₁
      ring_nf at h₁
      have hg₂ : x * y = l := by linarith
      exact ⟨hg₁, hg₂⟩
  -- extract 6 equations from the roots at P+Q, Q+R, P+R
  obtain ⟨h₁, h₂⟩ := hvieta (hpqt hpq.left) (hpqt hpq.right) hdist.left
  obtain ⟨h₃, h₄⟩ := hvieta (hqrt hqr.left) (hqrt hqr.right) hdist.right.left
  obtain ⟨h₅, h₆⟩ := hvieta (hprt hpr.left) (hprt hpr.right) hdist.right.right.symm
  -- use algebraic manipulatations to prove x = 3/2, y = -5/3 and in fact c = 52/19
  have hx : x = 3 / 2 := by linarith
  subst hx
  have hy : y = -5 / 3 := by linarith
  subst hy
  have hc : c = 52 / 19 := by linarith
  rw [hrmn] at hc
  -- finally prove that 52 = m, 19 = n so m + n = 71
  have hc : (m: ℚ)/n = 52 / 19 := by rify; assumption
  have : (m:ℤ) = 52 ∧ (n:ℤ) = 19 := by
    apply Rat.div_int_inj
    any_goals linarith
    any_goals assumption
    any_goals norm_cast
  norm_cast at this
  rw [this.left, this.right]