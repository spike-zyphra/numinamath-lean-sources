import Mathlib

open Polynomial

/-Let $a > 0$, and let $P(x)$ be a polynomial with integer coefficients such that
\[P(1) = P(3) = P(5) = P(7) = a\]and
\[P(2) = P(4) = P(6) = P(8) = -a.\]What is the smallest possible value of $a$?-/
theorem algebra_16405 {a : ℤ} (ha : a > 0) (P : Polynomial ℤ)
    (hP : P.eval 1 = a ∧ P.eval 3 = a ∧ P.eval 5 = a ∧ P.eval 7 = a)
    (hP' : P.eval 2 = -a ∧ P.eval 4 = -a ∧ P.eval 6 = -a ∧ P.eval 8 = -a) :
    a ≥ 315 := by
  -- There must be some polynomial $Q(x)$ such that $$P(x)-a=(x-1)(x-3)(x-5)(x-7)Q(x).$$
  have : ∃(P' : ℤ[X]), P' = P - a := by simp
  rcases this with ⟨P', hP''⟩
  have : P'.eval 2 = -2*a := by
    rw [hP'']
    simp
    rw [hP'.1]
    linarith
  have P'ne0 : P' ≠ 0 := by
    intro this
    have : P'.eval 2 = 0 := by
      rw [this]
      simp
    linarith

  have cons_le_of_not_mem {s t : Multiset ℤ} {a : ℤ} (hs : a ∉ s) : a ::ₘ s ≤ t ↔ a ∈ t ∧ s ≤ t := by
    apply Iff.intro (fun h ↦ ⟨Multiset.subset_of_le h (Multiset.mem_cons_self a s), le_trans (Multiset.le_cons_self s a) h⟩)
    rintro ⟨h₁, h₂⟩; rcases Multiset.exists_cons_of_mem h₁ with ⟨_, rfl⟩
    exact Multiset.cons_le_cons _ ((Multiset.le_cons_of_not_mem hs).mp h₂)

  have : ∃s : Multiset ℤ, s = {1, 3, 5, 7} := by simp
  rcases this with ⟨s, hs⟩
  have sleP'roots : s ≤ P'.roots := by
    rw [hs]
    apply (cons_le_of_not_mem ?hs).mpr
    case hs
    . -- 1 ∉ {3, 5, 7}
      simp
    -- 1 ∈ P'.roots ∧ {3, 5, 7} ≤ P'.roots
    constructor
    . -- 1 ∈ P'.roots
      simp
      constructor
      . -- P' ≠ 0
        exact P'ne0
      . -- P'.eval 1 = 0
        rw [hP'']
        simp
        rw [hP.1, sub_self]
    -- {3, 5, 7} ≤ P'.roots
    apply (cons_le_of_not_mem ?hs').mpr
    case hs'
    . -- 3 ∉ {5, 7}
      simp
    -- 3 ∈ P'.roots ∧ {5, 7} ≤ P'.roots
    constructor
    . -- 3 ∈ P'.roots
      simp
      constructor
      . -- P' ≠ 0
        exact P'ne0
      . -- P'.eval 3 = 0
        rw [hP'']
        simp
        rw [hP.2.1, sub_self]
    -- {5, 7} ≤ P'.roots
    apply (cons_le_of_not_mem ?hs'').mpr
    case hs''
    . -- 5 ∉ {7}
      simp
    -- 5 ∈ P'.roots ∧ 7 ≤ P'.roots
    constructor
    . -- 5 ∈ P'.roots
      simp
      constructor
      . -- P' ≠ 0
        exact P'ne0
      . -- P'.eval 5 = 0
        rw [hP'']
        simp
        rw [hP.2.2.1, sub_self]
    -- 7 ≤ P'.roots
    simp
    constructor
    . -- P' ≠ 0
      exact P'ne0
    . -- P'.eval 7 = 0
      rw [hP'']
      simp
      rw [hP.2.2.2, sub_self]

  have : ∃(Q : ℤ[X]), P' = (X - C 1)*(X - C 3)*(X - C 5)*(X - C 7)*Q := by
    apply exists_eq_mul_right_of_dvd
    have : (X - C 1)*(X - C 3)*(X - C 5)*(X - C 7) = (s.map fun a => X - C a).prod := by
      rw [hs]
      simp
      repeat rw [←mul_assoc]
    rw [this]
    apply (Multiset.prod_X_sub_C_dvd_iff_le_roots P'ne0 s).mpr
    exact sleP'roots
  rcases this with ⟨Q, hQ⟩

  -- Then, plugging in values of $2,4,6,8,$ we get
  -- P(2)-a = (2-1)(2-3)(2-5)(2-7)Q(2) = -15Q(2) = -2a
  have P'2 : P'.eval 2 = -2*a := by
    rw [hP'']
    simp
    rw [hP'.1]
    linarith
  have P'2' : P'.eval 2 = -15 * Q.eval 2 := by
    rw [hQ]
    simp
  -- P(4)-a=(4-1)(4-3)(4-5)(4-7)Q(4) = 9Q(4) = -2a
  have P'4 : P'.eval 4 = -2*a := by
    rw [hP'']
    simp
    rw [hP'.2.1]
    linarith
  have P'4' : P'.eval 4 = 9 * Q.eval 4 := by
    rw [hQ]
    simp
  -- P(6)-a=(6-1)(6-3)(6-5)(6-7)Q(6) = -15Q(6) = -2a
  have P'6 : P'.eval 6 = -2*a := by
    rw [hP'']
    simp
    rw [hP'.2.2.1]
    linarith
  have P'6' : P'.eval 6 = -15 * Q.eval 6 := by
    rw [hQ]
    simp
  -- P(8)-a=(8-1)(8-3)(8-5)(8-7)Q(8) = 105Q(8) = -2a
  have P'8 : P'.eval 8 = -2*a := by
    rw [hP'']
    simp
    rw [hP'.2.2.2]
    linarith
  have P'8' : P'.eval 8 = 105 * Q.eval 8 := by
    rw [hQ]
    simp

  -- That is, -2a=-15Q(2)=9Q(4)=-15Q(6)=105Q(8)
  -- Thus, `a` must be a multiple of lcm(15,9,15,105)=315.
  rw [P'2] at P'2'
  rw [P'4] at P'4'
  rw [P'6] at P'6'
  rw [P'8] at P'8'
  have dvd15 : 15 ∣ a := by
    have : 15 ∣ -2*a := by
      rw [P'2']
      simp
    exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
  have dvd9 : 9 ∣ a := by
    have : 9 ∣ -2*a := by
      rw [P'4']
      simp
    exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
  -- P'6' is same as P'2'
  have dvd105 : 105 ∣ a := by
    have : 105 ∣ -2*a := by
      rw [P'8']
      simp
    exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
  have : ∃n, a = 315*n := by
    apply dvd_def.mp
    -- this step is a bit tedious, only calculate it
    have : (315 : ℤ) = lcm 105 (lcm 15 9)  := by decide
    rw [this]
    apply lcm_dvd
    . -- 105 ∣ a
      exact dvd105
    . -- lcm 15 9 ∣ a
      apply lcm_dvd
      . -- 15 ∣ a
        exact dvd15
      . -- 9 ∣ a
        exact dvd9
  rcases this with ⟨n, hn⟩
  -- Then, n ≥ 1
  have : 0 < 315 * n := by linarith
  have : 0 < n := by apply pos_of_mul_pos_right this (by linarith)
  have : 1 ≤ n := by linarith
  linarith
