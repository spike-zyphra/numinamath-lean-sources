import Mathlib

/-- In the equation below, $A$ and $B$ are consecutive positive integers, and $A$, $B$, $A+B$ represent number bases:
$ 132_A+43_B=69_{A+B} $.
What is $A+B$?
(A) 9 (B) 11 (C) 13 (D) 15 (E) 17 -/
theorem number_theory_95263 {A B : ℕ} (hA : A > 0) (hB : B > 0)
    (hAB : B = A + 1 ∨ B = A - 1) (h : Nat.ofDigits A [2, 3, 1] + Nat.ofDigits B [3,4] = Nat.ofDigits (A + B) [9,6]) :
    A + B = 13 := by
  -- Change the equation to base 10:
  -- $ A^2 + 3A + 2 + 4B + 3 = 6A + 6B + 9 $
  dsimp[Nat.ofDigits_cons] at h
  -- consider everything over the integers for more subtraction lemmas
  zify at hA hB h
  zify
  simp at h
  -- $ A^2 - 3A -2B - 4 = 0 $
  have eq : ↑A^2 - 3 * ↑A - 2 * ↑B - (4 : ℤ) = 0 := by linarith
  -- either $B = A + 1$ or $A = B + 1$
  rcases hAB with (rfl|rfl)
  · -- so either $A^2 - 5A -6 = 0$
    have eq' : ↑ A^2 - 5 * ↑ A - (6 : ℤ) = 0 := by rw[Nat.cast_add, Nat.cast_one] at eq; omega
    -- which can be reexpressed as $(A-6)(A+1) = 0$, $B = A+1$
    have eq'' : (↑ A - 6) * (↑ A + (1 : ℤ)) = 0 := by linarith
    rw[mul_eq_zero] at eq''
    rcases eq'' with (eq''|eq'')
    -- then, $A = 6, B = 7$ and $A + B = 13$
    · rw[sub_eq_zero] at eq''
      rw[eq'', Nat.cast_add, Nat.cast_one, eq'']
      rfl
    -- since $A$ must be positive
    · rw[Nat.cast_add, Nat.cast_one, eq''] at hB
      exfalso
      exact lt_irrefl _ hB
  -- or $A^2 - 5A - 2 = 0$
  · have le : 1 ≤ A := by
      rw[← Nat.cast_zero, Nat.cast_lt] at hA
      rwa[Order.one_le_iff_pos]
    rw[Nat.cast_sub le, sub_pos] at hB
    have eq' : ↑ A^2 - 5 * ↑ A - (2 : ℤ) = 0 := by
      rw[Nat.cast_sub le, Nat.cast_one] at eq; linarith
    have eq'' : ↑ A^2 = 5 * ↑ A + (2 : ℤ) := by rw[← sub_eq_zero, ← sub_sub, eq']
    -- but then, $A \le 6$
    have ltfive : ↑ A ≤ (6 : ℤ) := by
      rw[← not_lt]
      intro lt
      have square_lt : (6 : ℤ) * A < A^2 := by
        rw[pow_two, mul_lt_mul_right] <;> assumption
      -- since for $A > 6$, $5A + 2 < A^2$ contrary to the assumption
      have : (5 : ℤ) * ↑A + 2 < ↑A ^ 2 := by
        trans 6 * A <;> linarith
      rw[← eq''] at this
      exact lt_irrefl _ this
    -- hence $0 < A \le 6$
    have : (A : ℤ) ∈ Finset.Ioc 0 6 := by simp[hA, ltfive]
    -- but none of the possible values are roots, hence the second case has no integer roots
    fin_cases this <;> {exfalso; simp at eq'}