import Mathlib

/- Suppose the function $f(x)$ is defined explicitly by the table $$\begin{array}{c || c | c | c | c | c}
x & 0 & 1 & 2 & 3 & 4 \\
\hline
f(x) & 0 & 0 & 1 & 3 & 6
\end{array}$$ This function is defined only for the values of $x$ listed in the table.

Suppose $g(x)$ is defined as $f(x)-x$ for all numbers $x$ in the domain of $f.$ How many distinct numbers are in the range of $g(x)?$ -/
theorem algebra_21824 (f g : Fin 5 → ℤ) (hf : f = ![0, 0, 1, 3, 6]) (hg : g = f - (fun (x : Fin 5) ↦ (x : ℤ))) : Set.ncard (Set.range g) = 3 := by
  -- $g(0)=0, g(1)=-1, g(2)=-1, g(3)=0, g(4)=2$
  have geq : g = ![0, -1, -1, 0, 2] := by
    rw [hg, hf]
    exact Matrix.dotProduct_eq (![0, 0, 1, 3, 6] - fun x => ↑↑x) ![0, -1, -1, 0, 2] (congrFun rfl)
  refine Set.ncard_eq_three.mpr ?_
  -- the range of $g$ consists of three distinct values $-1, 0, 2$
  use -1
  use 0
  use 2
  simp only [Int.reduceNeg, ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true, reduceCtorEq,
    OfNat.zero_ne_ofNat, true_and]
  ext x
  constructor
  · -- if $x \in \range (g)$ then $x = -1, 0, 2$
    intro xin
    rcases xin with ⟨i, hi⟩
    fin_cases i
    · -- if $x = g(0)$
      rw [hi.symm]
      simp only [Int.reduceNeg, geq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Set.mem_insert_iff, zero_eq_neg, one_ne_zero, Set.mem_singleton_iff, OfNat.zero_ne_ofNat, or_false, or_true]
    · -- if $x = g(1)$
      rw [hi.symm]
      simp only [Int.reduceNeg, geq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Set.mem_insert_iff, neg_eq_zero, one_ne_zero, Set.mem_singleton_iff, or_self, or_false]
      aesop
    · -- if $x = g(2)$
      rw [hi.symm]
      simp only [Int.reduceNeg, geq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Set.mem_insert_iff, neg_eq_zero, one_ne_zero, Set.mem_singleton_iff, or_self, or_false]
      aesop
    · -- if $x = g(3)$
      rw [hi.symm]
      simp only [Int.reduceNeg, geq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, Set.mem_insert_iff, zero_eq_neg, one_ne_zero, Set.mem_singleton_iff, OfNat.zero_ne_ofNat, or_false, or_true]
    · -- if $x = g(4)$
      rw [hi.symm]
      simp only [Int.reduceNeg, geq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, Set.mem_insert_iff, OfNat.ofNat_ne_zero, Set.mem_singleton_iff, or_true]
  · -- if $x = -1, 0, 2$ then $x \in \range (g)$
    intro xin
    rcases xin with xeq | xeq | xeq
    · -- if $x = -1$ then $x = g(1)
      use 1
      rw [xeq, geq]
      exact rfl
    · -- if $x = 0$ then $x = g(0)
      use 0
      rw [xeq, geq]
      exact rfl
    · -- if $x = 2$ then $x = g(4)
      use 4
      rw [xeq, geq]
      exact rfl
