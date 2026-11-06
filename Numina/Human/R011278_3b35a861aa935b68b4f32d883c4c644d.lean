import Mathlib

open Polynomial

/-
09.2. On a faded piece of paper it is possible, with some effort, to discern the following:


$$

\left(x^{2}+x+a\right)\left(x^{15}-\ldots\right)=x^{17}+x^{13}+x^{5}-90 x^{4}+x-90

$$


Some parts have got lost, partly the constant term of the first factor of the left side, partly the main part of the other factor. It would be possible to restore the polynomial forming the other factor, but we restrict ourselves to asking the question: What is the value of the constant term a? We assume that all polynomials in the statement above have only integer coefficients.
 -/

-- lemma that a ∣ 90, 184 means a ∣ 2, their gcd
lemma l_gcd  {a b c : ℤ} (h1 : a * b = -90) (h2 : a * c = -184) : a ∣ 2 := by
  replace h1 : a ∣ -90 := by simp [← h1]
  replace h2 : a ∣ -184 := by simp [← h2]
  have h3 := Int.dvd_gcd h1 h2
  norm_num at h3
  assumption

-- if a ∣ b then a is from b's natural divisors or -a is from b's natural divisors
lemma l_divisor {a b : ℤ} (h : a ∣ b) (hb : b ≠ 0) : a ∈ b.natAbs.divisors.map ⟨(↑), Nat.cast_injective⟩ ∨
    -a ∈ b.natAbs.divisors.map ⟨(↑), Nat.cast_injective⟩ := by
  simp [hb]
  obtain ha | ha := le_total 0 a
  . left
    use a.natAbs
    simp [ha, h]
  . right
    use a.natAbs
    simp [ha, h]

theorem algebra_111373 (a : ℤ) (Q : ℤ[X]) (h : (X^2 + X + C a) * Q = (X^17 + X^13 + X^5 - 90 * X^4 + X - 90))
    : a = 2 := by
  -- name polynomials P, Q for ease of work
  let P := X^2 + X + C a
  let R : ℤ[X] := X^17 + X^13 + X^5 - 90 * X^4 + X - 90
  change P * Q = R at h
  -- evaluate at 0 and -1 and use lemma to get a ∣ 2
  have h_eval (x : ℤ) : P.eval x * Q.eval x = R.eval x := by simp [← h]
  have h_eval_0 := h_eval 0
  simp [P, R] at h_eval_0
  have h_eval_neg_1 := h_eval (-1)
  simp [P, R] at h_eval_neg_1
  have h_dvd_two := l_gcd h_eval_0 h_eval_neg_1
  -- use lemma to get a ∈ {1, 2} or -a in {-1, -2}
  replace h_dvd_two := l_divisor h_dvd_two (by norm_num)
  convert_to a ∈ ({1, 2} : Finset ℤ) ∨ -a ∈ ({1, 2} : Finset ℤ) at h_dvd_two
  simp at h_dvd_two
  rw [neg_eq_iff_eq_neg, neg_eq_iff_eq_neg] at h_dvd_two
  -- casework on all values of a, evaluation of equation at 1 or 2 generally disprove cases except a = 2
  obtain (rfl | rfl) | (rfl | rfl) := h_dvd_two
  . have h_eval_1 := h_eval 1
    simp [P, R] at h_eval_1
    omega
  . rfl
  . have h_eval_2 := h_eval 2
    simp [P, R] at h_eval_2
    omega
  . have h_eval_1 := h_eval 1
    simp [P, R] at h_eval_1