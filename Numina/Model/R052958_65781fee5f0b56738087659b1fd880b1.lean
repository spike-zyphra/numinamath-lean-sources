import Mathlib

theorem number_theory_92514 (x : ℤ) :
    ∃ n, n^2 = x^4 + x^3 + x^2 + x + 1 ↔ x = -1 ∨ x = 0 ∨ x = 3 := by
  by_cases h₁ : x ≤ 0
  · -- Let `n` be 1
    use 1
    constructor
    · -- Forward direction: if $1^2 = x^4 + x^3 + x^2 + x + 1$, then $x = -1$ or $x = 0$ or $x = 3$
      intro h
      have eq : x^4 + x^3 + x^2 + x + 1 = 1 := by linarith
      have eq2 : x^4 + x^3 + x^2 + x = 0 := by linarith
      have eq3 : x * (x^3 + x^2 + x + 1) = 0 := by
        ring_nf at eq2 ⊢
        linarith
      cases' (mul_eq_zero.mp eq3) with hx hx
      · -- Case $x = 0$
        right
        left
        linarith
      · -- Case $x^3 + x^2 + x + 1 = 0$
        have eq4 : x^3 + x^2 + x + 1 = (x + 1) * (x^2 + 1) := by ring
        rw [eq4] at hx
        cases' (mul_eq_zero.mp hx) with hx1 hx2
        · -- Case $x + 1 = 0$
          left
          linarith
        · -- Case $x^2 + 1 = 0$
          have h2 : x^2 + 1 > 0 := by nlinarith
          have : x^2 + 1 = 0 := by nlinarith
          nlinarith
    · -- Backward direction: if $x = -1$ or $x = 0$, then $1^2 = x^4 + x^3 + x^2 + x + 1$
      rintro (h | h | h)
      · -- Case $x = -1$
        rw [h]
        norm_num
      · -- Case $x = 0$
        rw [h]
        norm_num
      · -- Case $x = 3$
        exfalso
        linarith
  · -- Case x > 0
    use 11
    constructor
    · -- Forward direction: if $11^2 = x^4 + x^3 + x^2 + x + 1$, then $x = 3$
      intro h
      have eq1 : x^4 + x^3 + x^2 + x + 1 = 121 := by
        nlinarith
      have eq2 : x ≤ 3 := by
        nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - x + 1)]
      have eq3 : x ≥ 3 := by
        nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - x + 1)]
      have eq4 : x = 3 := by omega
      tauto
    · -- Backward direction: if $x = 3$, then $11^2 = x^4 + x^3 + x^2 + x + 1$
      rintro (h | h | h)
      · -- Case $x = -1$
        exfalso
        linarith
      · -- Case $x = 0$
        exfalso
        linarith
      · -- Case $x = 3$
        rw [h]
        norm_num