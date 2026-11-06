import Mathlib

open Real Set
open scoped BigOperators

/- 1st Irish 1988 Problem 7 Put f(x) = x^3 - x. Show that the set of positive real A such that for some real x we have f(x + A) = f(x) is the interval (0, 2]. -/

-- lemma that in reals discriminant being nonegative is equivlaent to solution existing for quadratic equations
lemma l_qudratic_soln_iff {a b c : ℝ} (ha : a ≠ 0) : (∃ x, a * (x * x) + b * x + c = 0) ↔
    0 ≤ discrim a b c := by
  constructor
  . rintro ⟨x, hx⟩
    rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at hx
    rw [hx]
    positivity
  . rintro h
    apply exists_quadratic_eq_zero ha
    use √(discrim a b c)
    ring_nf
    rw [sq_sqrt h]

-- lemma that following disrciminant being nonnegative is equivlaent to A ≤ 2 if 0 < A
lemma l_discrim_ineq {A : ℝ} (ha : 0 < A) : 0 ≤ discrim (3 * A) (3 * A^2) (A^3 - A) ↔ A ≤ 2 := by
  simp [discrim]
  calc
    _ ↔ A^2 * A^2 ≤ 4 * A^2 := by
      constructor <;> (rintro h; linarith)
    _ ↔ A^2 ≤ 2^2 := by
      norm_num
      apply mul_le_mul_right
      nlinarith
    _ ↔ _ := by
      apply sq_le_sq₀
      . linarith
      . norm_num

theorem algebra_134686 {f : ℝ → ℝ} (hf : f = λ x => x ^ 3 - x) :
    {A | 0 < A ∧ ∃ x, f (x + A) = f x} = Ioc 0 2 := by
  -- first simplify the f and write equivalent format in quadratic equation
  have h1 (x A : ℝ) : f (x + A) = f x ↔ (3 * A) * (x * x) + (3 * A^2) * x + (A^3 - A) = 0 := by
    simp [hf]
    constructor <;> (rintro h; linarith)
  simp_rw [h1]
  -- now first convert it to discriminant being nonnegative, convert it to (0, 2] using second lemma
  calc
    _ = {A : ℝ | 0 < A ∧ 0 ≤ discrim (3 * A) (3 * A^2) (A^3 - A)} := by
      ext A; simp
      rintro hA
      apply l_qudratic_soln_iff
      positivity
    _ = {A : ℝ | 0 < A ∧ A ≤ 2} := by
      ext A; simp
      rintro hA
      rw [l_discrim_ineq hA]