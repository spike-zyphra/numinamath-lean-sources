import Mathlib

/- Show that if \( a_{j} \equiv b_{j} \pmod{m} \) for \( j=1,2, \ldots, n \), where \( m \) is a positive integer and \( a_{j}, b_{j}, j=1,2, \ldots, n \) are integers, then:
a) \( \sum_{j=1}^{n} a_{j} \equiv \sum_{j=1}^{n} b_{j} \pmod{m} \)
b) \( \prod_{j=1}^{n} a_{j} \equiv \prod_{j=1}^{n} b_{j} \pmod{m} \).
-/
theorem number_theory_4657 (m n : ℕ) (a b : Fin n → ℤ)
                           (hm : m > 0)
                           (hequiv : ∀ j : Fin n, a j ≡ b j [ZMOD m]) :
                           ∑ j : Fin n, a j ≡ ∑ j : Fin n, b j [ZMOD m] ∧
                           ∏ j : Fin n, a j ≡ ∏ j : Fin n, b j [ZMOD m] := by
  constructor
  · -- First, we prove that \( \sum_{j=1}^n a j \equiv \sum_{j=1}^n b j \mod m \).
    -- We will use mathematical induction on \( n \).
    induction n with
    | zero =>
      -- When \( n = 0 \), this statement is obviously true.
      simp_all
    | succ n h =>
      -- Next, we assume that the statement holds for \( n = i \), and we need to prove that it also holds for \( n = i + 1 \).
      -- That is, we need to prove \( \sum_{j=1}^{n+1} a j \equiv \sum_{j=1}^{n+1} b j \mod m \).
      -- First, we rewrite the target \( \sum_{j=1}^{n+1} a j \equiv \sum_{j=1}^{n+1} b j \mod m \) as \( \sum_{j=1}^n a j + a (n+1) \equiv \sum_{j=1}^n b j + b (n+1) \mod m \).
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      -- Therefore, we only need to prove \( \sum_{j=1}^n a j \equiv \sum_{j=1}^n b j \mod m \) and \( a (n+1) \equiv b (n+1) \mod m \).
      apply Int.ModEq.add
      · -- For the first subgoal, we can directly use the assumption from the induction step.
        let a' := fun (i : Fin n) => a i.castSucc
        let b' := fun (i : Fin n) => b i.castSucc
        have hequiv' : ∀ i : Fin n, a' i ≡ b' i [ZMOD m] := fun i => hequiv i.castSucc
        exact h a' b' hequiv'
      · -- For the second subgoal, we can directly use the original condition from the problem.
        exact hequiv (Fin.last n)
  · -- Next, we prove \( \prod_{j=1}^n a j \equiv \prod_{j=1}^n b j \mod m \).
    -- We will use mathematical induction on \( n \).
    induction n with
    | zero =>
      -- When \( n = 0 \), this statement is obviously true.
      simp_all
    | succ n h =>
      -- Next, we assume that the statement holds for \( n = i \), and we need to prove that it also holds for \( n = i + 1 \).
      -- That is, we need to prove \( \prod_{j=1}^{n+1} a j \equiv \prod_{j=1}^{n+1} b j \mod m \).
      -- First, we rewrite the target \( \prod_{j=1}^{n+1} a j \equiv \prod_{j=1}^{n+1} b j \mod m \) as \( \prod_{j=1}^n a j \cdot a (n+1) \equiv \prod_{j=1}^n b j \cdot b (n+1) \mod m \).
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      -- Therefore, we only need to prove \( \prod_{j=1}^n a j \equiv \prod_{j=1}^n b j \mod m \) and \( a (n+1) \equiv b (n+1) \mod m \).
      apply Int.ModEq.mul
      · -- For the first subgoal, we can directly use the assumption from the induction step.
        let a' := fun (i : Fin n) => a i.castSucc
        let b' := fun (i : Fin n) => b i.castSucc
        have hequiv' : ∀ i : Fin n, a' i ≡ b' i [ZMOD m] := fun i => hequiv i.castSucc
        exact h a' b' hequiv'
      · -- For the second subgoal, we can directly use the original condition from the problem.
        exact hequiv (Fin.last n)
  -- Thus, the original statement is proven.
