import Mathlib

/--
How many four-digit numbers $N$ have the property that the three-digit number obtained by removing the leftmost digit is one ninth of $N$?

$\mathrm{(A)}\ 4 \qquad\mathrm{(B)}\ 5 \qquad\mathrm{(C)}\ 6 \qquad\mathrm{(D)}\ 7 \qquad\mathrm{(E)}\ 8$
-/
theorem number_theory_95605 :
Set.ncard {N : ℕ | N ∈ Finset.Icc 1000 9999 ∧ (N % 1000) * 9 = N} = 7 := by
  -- Let $N = \overline{abcd} = 1000a + \overline{bcd}$, such that $\frac{N}{9} = \overline{bcd}$. Then $1000a + \overline{bcd} = 9\overline{bcd} \Longrightarrow 125a = \overline{bcd}$. We can also prove a ≤ 7.
  simp_rw [(by omega : ∀ N, N % 1000 * 9 = N ↔ 125 * (N / 1000) = N % 1000 ∧ N / 1000 ≤ 7)]
  -- Since $100 \le \overline{bcd} < 1000$, from $a = 1, \ldots, 7$ we have $7$ three-digit solutions
  -- 1125, 2250, 3375, 4500, 5625, 6750, 7875
  have factoid (N : ℕ) : N ∈ Finset.Icc 1000 9999 ∧ 125 * (N / 1000) = N % 1000 ∧ N / 1000 ≤ 7 ↔ N = 1125 ∨ N = 2250 ∨ N = 3375 ∨ N = 4500 ∨ N = 5625 ∨ N = 6750 ∨ N = 7875 := by
    constructor
    · intro fac
      simp only [Finset.mem_Icc] at fac
      -- Since a ≤ 7, we enumerate a from 0 to 7
      have des (N : ℕ) (h : N ≤ 7) : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 := by
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        cases' N with N
        · native_decide
        linarith
      -- We test each value and arrive at the list of possible four digit numbers
      rcases (des (N / 1000) (by tauto)) with des | des | des | des | des | des | des | des <;> try omega
    · intro fac
      rcases fac with des | des | des | des | des | des | des <;> rw [des] <;> native_decide
  -- These are the steps to make Lean count the elements when we have all possible values
  simp_rw [factoid]
  have dskl : {N | N = 1125 ∨ N = 2250 ∨ N = 3375 ∨ N = 4500 ∨ N = 5625 ∨ N = 6750 ∨ N = 7875} = {1125, 2250, 3375, 4500, 5625, 6750, 7875} := by
    aesop
  rw [dskl]
  (repeat rw [Set.ncard_insert_of_not_mem]) <;> try decide
  rw [Set.ncard_singleton]