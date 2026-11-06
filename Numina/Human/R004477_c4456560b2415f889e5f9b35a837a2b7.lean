import Mathlib


/- 6. Find all four-digit numbers $\overline{a b c d}$ (in decimal notation), for which the equality

$$
\overline{a b c d}+1=(\overline{a c}+1)(\overline{b d}+1) .
$$

holds. -/
theorem number_theory_272462 {a b c d: ℕ}
  (ha: 1 ≤  a ∧ a ≤ 9) (hb: 1 ≤ b ∧ b ≤ 9)
  (hc: 1 ≤ c ∧ c ≤ 9) (hd: 1 ≤ d ∧ d ≤ 9):
  Nat.ofDigits 10 [d, c, b, a] + 1 =
    (Nat.ofDigits 10 [c,a] + 1) * (Nat.ofDigits 10 [d,b] + 1) ↔
  (b = 9 ∧ c = 9 ∧ d = 9) := by

  -- original equation simplifies to
  -- 100a(9-b) + 10a(9-d) + 10b(9-c) + c(9-d) = 0
  have: Nat.ofDigits 10 [d, c, b, a] + 1 =
    (Nat.ofDigits 10 [c,a] + 1) * (Nat.ofDigits 10 [d,b] + 1) ↔
    100*a*(9-b) + 10*a*(9-d) + 10*b*(9-c) + c*(9-d:ℤ) = 0 := by
    have h1: Nat.ofDigits 10 [c,a] = c + 10*a := rfl
    have h2: Nat.ofDigits 10 [d,c,b,a] = d + 10*c + 100*b + 1000*a := by
      dsimp [Nat.ofDigits]
      ring
    have h3: Nat.ofDigits 10 [d,b] = d + 10*b := rfl
    rw [h1, h2, h3]
    zify
    constructor <;> intro h <;> linarith only [h]
  rw [this]

  -- since a,b,c,d are digits of decimal notation numbers, each term ≥ 0.
  have h1: (c:ℤ) * (9-d) ≥ 0 := by
    apply mul_nonneg (by simp) (by linarith only [hd])
  have h2: b*(9-c:ℤ) ≥ 0 := by
    apply mul_nonneg (by simp) (by linarith only [hc])
  replace h2: 10*b*(9-c:ℤ) ≥ 0 := by linarith only [h2]
  have h3: a*(9-d:ℤ) ≥ 0 := by
    apply mul_nonneg (by simp) (by linarith only [hd])
  replace h3: 10*a*(9-d:ℤ) ≥ 0 := by linarith only [h3]
  have h4: a*(9-b:ℤ) ≥ 0 := by
    apply mul_nonneg (by simp) (by linarith only [hb])
  replace h4: 100*a*(9-b:ℤ) ≥ 0 := by linarith only [h4]

  -- then the sum = 0, forces both terms = 0
  have eq_zero_of_nng_add {x y: ℤ} (hx: x ≥ 0) (hy: y ≥ 0)
    (h: x+y = 0): x = 0 ∧ y = 0 := by
    have xeq: x = 0 := by
      by_contra!
      replace hx := lt_of_le_of_ne hx this.symm
      linarith only [h, hx, hy]
    have yeq: y = 0 := by
      by_contra!
      replace hy := lt_of_le_of_ne hy this.symm
      linarith only [h,hx, hy]
    exact ⟨xeq, yeq⟩

  -- so all those terms = 0, forces b=c=d=9
  constructor
  · intro heq
    have hh1: 100*a*(9-b) + 10*a*(9-d) + 10*b*(9-c) = (0:ℤ)
      ∧ c*(9-d) = (0:ℤ) := by
      apply eq_zero_of_nng_add ?_ h1 heq
      linarith only [h2, h3, h4]
    have hh2: 100*a*(9-b) + 10*a*(9-d) = (0:ℤ) ∧
      10*b*(9-c) = (0:ℤ) := by
      apply eq_zero_of_nng_add ?_ h2 hh1.left
      linarith only [h3, h4]
    have hh3 := eq_zero_of_nng_add h4 h3 hh2.left
    have anz: a ≠ 0 := by omega
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero,
    anz, or_self, false_or] at hh3
    have beq: b = 9 := by
      zify
      linarith only [hh3]
    have deq: d = 9 := by
      zify
      linarith only [hh3]
    simp only [beq, Nat.cast_ofNat, sub_self, mul_zero, deq,
    add_zero, Int.reduceMul, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or, true_and] at hh2
    have ceq: c = 9 := by
      zify
      linarith only [hh2]
    exact ⟨beq, ceq, deq⟩

  · -- given b,c,d = 9, each term is 0.
    rintro ⟨rfl, rfl, rfl⟩
    simp