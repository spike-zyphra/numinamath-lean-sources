import Mathlib

open Polynomial

/- 9. If $x_{1}, x_{2}$ are the real roots of the equation $x^{2}+a x+a-\frac{1}{2}=0$.
(1) Find the set of real values $A$ for $a$;
(2) Is there a real number $m$ such that the inequality $m^{2}+t m+4 \sqrt{2}+6 \geqslant\left(x_{1}-3 x_{2}\right)\left(x_{2}-3 x_{1}\right)$ holds for any $a \in A$ and $t \in[-1,1]$? If it exists, find the range of $m$; if not, explain the reason. -/

-- the polynomial is monic
lemma l_monic {b c : ℝ} : (X^2 + C b * X + C c).Monic := by
  rw [Monic.def, ← coeff_natDegree ]
  have : (X^2 + C b * X + C c).natDegree = 2 := by compute_degree!
  rw [this]
  simp

-- the polynomial splits due to two roots
lemma l_splits {b c x1 x2 : ℝ} (h : (X^2 + C b * X + C c).roots = {x1, x2}) : Splits (RingHom.id ℝ)
    ((X^2 + C b * X + C c)) := by
  rw [Polynomial.splits_iff_card_roots]
  have : (X^2 + C b * X + C c).natDegree = 2 := by compute_degree!
  rw [this, h]
  simp

-- the polynomial has two roots then evaluation at all x is (x - x1) * (x - x2)
lemma l_quadratic_roots_eq_iff {b c x1 x2 : ℝ} : (X ^ 2 + C b * X + C c).roots = {x1, x2} ↔
    (∀ x, x^2 + b * x + c = (x - x1) * (x - x2)) := by
  calc
    -- roots is x1, x2 then polynomial is (X - x1) * (X - x2), then all evaluations match is sufficient
    _ ↔ X^2 + C b * X + C c = (X - C x1) * (X - C x2) := by
      constructor <;> rintro h
      . convert Polynomial.eq_prod_roots_of_monic_of_splits_id l_monic (l_splits h)
        rw [h]
        simp
      . rw [h, ← Polynomial.roots_multiset_prod_X_sub_C (s := {x1, x2})]
        simp
    _ ↔ ∀ x, x^2 + b * x + c = (x - x1) * (x - x2) := by
      constructor <;> rintro h
      . rintro x
        have := congrArg (fun P ↦ P.eval x) h
        simpa using this
      . apply Polynomial.funext
        simpa

-- discirminant nonegative is equivalent to two x1, x2 such that (x - x1) * (x - x2) is quadratic
lemma l_discrim_factor {b c : ℝ} : (∃ x1 x2, ∀ (x : ℝ), x ^ 2 + b * x + c = (x - x1) * (x - x2)) ↔
    0 ≤ discrim 1 b c := by
  constructor <;> rintro h
  . obtain ⟨x1, x2, hx⟩ := h
    specialize hx x1
    simp at hx
    rw [sq, ← one_mul (a := x1 * x1)] at hx
    rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)] at hx
    rw [hx]
    positivity
  . use (-b + √(discrim 1 b c))/2, (-b - √(discrim 1 b c))/2
    rintro x
    ring_nf
    rw [Real.sq_sqrt h, discrim]
    ring

-- lemma from newer version of mathlib
lemma sub_mul_sub_nonneg_iff (x : ℝ) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
    and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]


theorem algebra_150646_1 (a : ℝ) : (∃ (x1 x2 : ℝ), (X^2 + C a * X + C (a - 1 / 2)).roots = {x1, x2}) ↔
    a ≤ 2 - √2 ∨ 2 + √2 ≤ a := by
  -- first problem two roots being x1 x2 means for all x the value is (x - x1) * (x - x2) from lemmas
  simp_rw [l_quadratic_roots_eq_iff]
  rw [l_discrim_factor, discrim]
  -- the discriminant inequality can be transformed by sub_mul_sub_nonneg_iff
  conv_lhs => arg 2; equals (a - (2 - √2)) * (a - (2 + √2)) =>
    ring_nf; simp; ring
  rw [sub_mul_sub_nonneg_iff]
  linarith [show 0 ≤ √2 by positivity]

theorem algebra_150646_2 (m : ℝ) :
    (∀ t ∈ Set.Icc (-1) 1, ∀ (a x1 x2 : ℝ), (X^2 + C a * X + C (a - 1 / 2)).roots = {x1, x2} →
    (x1 - 3*x2) * (x2 - 3*x1) ≤ m^2 + t * m + 4*√2 + 6) ↔ m = 0 ∨ m ≤ -1 ∨ 1 ≤ m := by
  --first of all x1, x2 being root means we can transform the lhs (x1 - 3*x2) * (x2 - 3*x1) by vieta
  have h1 (t a x1 x2 : ℝ) : ((X^2 + C a * X + C (a - 1 / 2)).roots = {x1, x2} →
    (x1 - 3*x2) * (x2 - 3*x1) ≤ m^2 + t * m + 4*√2 + 6) ↔ ((X^2 + C a * X + C (a - 1 / 2)).roots = {x1, x2} →
    16 * (a - 1/2) - 3 * (-a)^2 ≤ m^2 + t * m + 4*√2 + 6) := by
    convert_to (X^2 + C a * X + C (a - 1 / 2)).roots = {x1, x2} → ((x1 - 3*x2) * (x2 - 3*x1) ≤ m^2 + t * m + 4*√2 + 6 ↔ 16 * (a - 1/2) - 3 * (-a)^2 ≤ m^2 + t * m + 4*√2 + 6)
    . tauto
    rintro h
    have h2 : x1 + x2 = -a := by
      suffices a = - (x1 + x2) by linarith
      convert sum_roots_eq_nextCoeff_of_monic_of_split l_monic (l_splits h)
      . simp [nextCoeff, show (X ^ 2 + C a * X + (C a - C 2⁻¹)).natDegree = 2 by compute_degree!]
      . rw [h]
        simp
    have h3 : x1 * x2 = a - 1 / 2 := by
      rw [eq_comm]
      convert prod_roots_eq_coeff_zero_of_monic_of_splits l_monic (l_splits h) using 1
      . simp
      . have : (X ^ 2 + C a * X + C (a - 1 / 2)).natDegree = 2 := by compute_degree!
        rw [this]
        rw [h]
        simp
    rw [← h2, ← h3]
    ring_nf
  simp_rw [h1]
  clear h1
  constructor <;> rintro h
  -- left to right, speciazlie hypothesis at 1, (2 + √2), (-1-√2/2), (-1-√2/2)
  . have hp : (X ^ 2 + C (2 + √2) * X + C (2 + √2 - 1 / 2)).roots = {-1 - √2 / 2,-1 - √2 / 2} := by
      rw [l_quadratic_roots_eq_iff]
      rintro x
      ring_nf; simp; ring_nf
    have h1 := h 1 (by simp) (2 + √2) (-1 - √2/2) (-1 - √2/2) hp
    ring_nf at h1
    simp at h1
    ring_nf at h1
    -- we get following, which means m ≤ -1 or 0 ≤ m
    have h2 : 0 ≤ (m - -1) * (m - 0) := by linarith
    rw [sub_mul_sub_nonneg_iff _ (by norm_num)] at h2
    -- speciazlie hypothesis at -1, (2 + √2), (-1-√2/2), (-1-√2/2)
    have h3 := h (-1) (by simp) (2 + √2) (-1 - √2/2) (-1 - √2/2) hp
    ring_nf at h3
    simp at h3
    ring_nf at h3
    -- we get following, which means m ≤ 0 or 1 ≤ m
    have h4 : 0 ≤ (m - 0) * (m - 1) := by linarith
    rw [sub_mul_sub_nonneg_iff _ (by norm_num)] at h4
    -- combining ranges of m we get goal
    obtain h2 | h2 := h2
    . right; left; assumption
    . obtain h4 | h4 := h4
      . left; linarith
      . right; right; assumption
  -- right to left, use first part of problem to get range of a
  . rintro t ht a x1 x2 hx
    have hx' := algebra_150646_1 _ |>.mp ⟨x1, x2, hx⟩
    conv_lhs => equals -3 * (a - 8/3)^2 + 64/3 - 8 => ring
    -- the lhs of inequality is ≤ value at 2 + √2 (mainly due to axis of symmetry at 8/3 is closer to 2 + √2 of a's range)
    have : -3 * (a - 8 / 3) ^ 2 + 64 / 3 - 8 ≤ -3 * (2 + √2 - 8 / 3) ^ 2 + 64 / 3 - 8 := by
      suffices (a - 8 / 3) ^ 2 ≥ (2 + √2 - 8 / 3) ^ 2 by linarith
      have ht : √(4 / 9) ≤ √2 := by
        apply Real.sqrt_le_sqrt
        norm_num
      have : 2 - √2 ≤ 8 / 3 := by
        suffices √((-2 / 3)^2) ≤ √2 by
          rw [← neg_sq, Real.sqrt_sq (by norm_num)] at this
          linarith
        norm_num at ht ⊢
        assumption
      have : 8 / 3 ≤  2 + √2 := by
        suffices √((2 / 3)^2) ≤ √2 by
          rw [Real.sqrt_sq (by norm_num)] at this
          linarith
        norm_num at ht ⊢
        assumption
      obtain hx' | hx' := hx'
      . rw [← neg_sq, ge_iff_le, sq_le_sq₀] <;> linarith
      . rw [ge_iff_le, sq_le_sq₀] <;> linarith
    -- so enough to prove rhs is greater than value at 2 + √2
    trans -3 * (2 + √2 - 8 / 3) ^ 2 + 64 / 3 - 8
    . assumption
    . ring_nf
      simp
      -- have to prove 0 ≤ m^2 + t*m
      suffices 0 ≤ m^2 + t * m by linarith
      simp at ht
      -- casework on m's ranges and show inequality
      obtain rfl | hm | hm := h
      . simp
      . suffices (-m) * (m + t) ≤ 0 by linarith
        apply mul_nonpos_of_nonneg_of_nonpos
        . linarith
        . linarith
      . suffices 0 ≤ m * (m + t) by linarith
        apply mul_nonneg
        . linarith
        . linarith