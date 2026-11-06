import Mathlib

open Polynomial Complex

/- Let P(z)=z^3+az^2+bz+c, where a, b, and c are real.
There exists a complex number w such that the three roots of P(z) are w+3i, w+9i, and 2w−4,
where i^2=−1. Find ∣a+b+c∣. -/
theorem algebra_94704 (a b c : ℝ) (w : ℂ)
    (hroots : (X^3 + C (a : ℂ) * X ^ 2 + C (b : ℂ) * X + C (c : ℂ)).roots = {w + 3 * I, w + 9 * I, 2 * w - 4}) :
    |a + b + c| = 136 := by
  -- let P be the polynomial X ^ 3 + a * X ^ 2 + b * X + c
  set P : ℂ[X] := X ^ 3 + _ + _ + _
  -- the degree of P is 3
  have hdeg : P.natDegree = 3 := by simp [P]; compute_degree <;> norm_num
  -- P is monic
  have hmonic : P.Monic := by rw [Monic.def, leadingCoeff, hdeg]; simp [P]
  -- P has exactly 3 roots
  have hcard : P.roots.card = P.natDegree := by simp [hroots, hdeg]
  -- P splits over ℂ (since its degree equals to the number of roots)
  have hsplits : P.Splits (RingHom.id ℂ) := by rw [splits_iff_card_roots, hcard]
  -- use Vieta's formula to compute a = -∑ roots
  have ha : a = 4 - 4 * w - 12 * I :=
    calc
      a = P.nextCoeff := by simp [nextCoeff, hdeg, P]
      _ = -P.roots.sum := sum_roots_eq_nextCoeff_of_monic_of_split hmonic hsplits
      _ = _ := by simp [hroots]; ring
  -- a ∈ ℝ, so a.im = 0 and we find that w.im = -3
  have hwim : w.im = -3 := by
    apply_fun Complex.im at ha
    field_simp at ha
    linarith
  -- use Vieta's formula to compute b
  have hb : b = (w + 3 * I) * (2 * w - 4) + ((w + 9 * I) * (2 * w - 4) + (w + 3 * I) * (w + 9 * I)) :=
    calc
      b = P.coeff 1 := by simp [P]
      _ = P.leadingCoeff * (-1) ^ (P.natDegree - 1) * P.roots.esymm (P.natDegree - 1) := by
        apply coeff_eq_esymm_roots_of_card hcard
        simp [hdeg]
      _ = _ := by
        rw [hroots, leadingCoeff, hdeg]
        simp [P, Multiset.esymm, Multiset.powersetCard_one]
  -- use Vieta's formula to compute c
  have hc : c = -(w + 3 * I) * (w + 9 * I) * (2 * w - 4) :=
    calc
      c = P.coeff 0 := by simp [P]
      _ = (-1) ^ P.natDegree * P.roots.prod := prod_roots_eq_coeff_zero_of_monic_of_splits hmonic hsplits
      _ = _ := by simp [hroots, hdeg]; ring
  -- show that w.re = 4
  have hwre : w.re = 4 := by
    -- c ∈ ℝ, so c.im = 0
    apply_fun Complex.im at hc
    field_simp [hwim] at hc
    -- we find that 6 * w.re * (4 - w.re) = 0
    have heq : 6 * w.re * (4 - w.re) = 0 := by rw [hc]; ring
    simp [mul_eq_zero] at heq
    -- we have w.re = 0 or w.re = 4. Prove that w.re = 0 is impossible
    cases' heq with h h <;> [skip; linarith]
    -- assume that w.re = 0 and compute b.im
    apply_fun Complex.im at hb
    -- we get 0 = b.im = -24, a contradiciton
    field_simp [hwim, h, pow_two] at hb
  -- we obtained that w = 4 - 3 * I
  -- now we can compute a, b, c and find the absolute value of their sum
  rw [←ofReal_re a, ←ofReal_re b, ←ofReal_re c, ha, hb, hc]
  field_simp [hwim, hwre, pow_two]
  norm_num