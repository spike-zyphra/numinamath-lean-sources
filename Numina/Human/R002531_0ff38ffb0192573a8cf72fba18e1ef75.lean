import Mathlib

/-A sequence of integers a_1,a_2,a_3,⋯ is chosen so that a_n=a_{n-1}-a_{n-2}for each n≥3. What is the sum of the first 2001 terms of this sequence if the sum of the first 1492 terms is 1985, and the sum of the first 1985 terms is 1492?-/
theorem AIME_Algebra_94817 {a : ℕ → ℤ} (h : ∀ n, a (n + 2) = a (n + 1) - a n)
(h1 : ∑ i in Finset.range 1492, a i = 1985) (h2 : ∑ i in Finset.range 1985, a i = 1492) :
∑ i in Finset.range 2001, a i = 986 := by
--We have a recursion formula, so we want to express all summation in terms of the first two elements of this sequence.
  set x:=a 0 with xdef
  set y:=a 1 with ydef
--We note that a i= - a (i+3), so the sum of consequetive 6 terms cancels.
  have step3:∀ i, a i=- a (i+3):=by
    intro i
    rw[show (i+3=(i+1)+2) by norm_num,h,add_assoc,one_add_one_eq_two,h]
    ring
  have step6:∀ n, ∑ i in Finset.range n, a i=∑ i in Finset.range (n+6), a i:=by
    intro n
    rw[show (n+6=n.succ.succ.succ.succ.succ.succ) by norm_num]
    rw[Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
    rw[step3 n,step3 (n+1),step3 (n+2)]
    rw[add_assoc n]
    simp only [Nat.reduceAdd]
    ring
--We know that for every m, the sum from a n to a (n+6*m) is zero, thus the sum from a 0 to a n is the same as the sum from a 0 to a (n+6 * m).
  have hsum:∀ n m, ∑ i in Finset.range n, a i=∑ i in Finset.range (n+6*m), a i:=by
    intro n m
    induction' m with m ih
    norm_num
    rw[show (n+6*(m+1)=(n+6*m+6)) by rfl,←step6,ih]
--Now we can reduce all assumption to a finite sum with range below 6.
  rw[show (1492=4+6*248) by norm_num,←hsum] at h1
  rw[show (1985=5+6*330) by norm_num,←hsum] at h2
  rw[show (2001=3+6*333) by norm_num,←hsum]
--We calculate each term.
  have a2:a 2=y-x:=by rw[←zero_add 2,h,zero_add,xdef,ydef]
  have a3:a 3=-x:=by rw[xdef,step3 0,neg_neg]
  have a4:a 4=-y:=by rw[ydef,step3 1,neg_neg]
  have a5:a 5=-(y-x):=by rw[←a2,step3 2,neg_neg]
--We express each summation as an addition.
  replace h1:a 0+a 1 +a 2+a 3=1985:=by
    rw[←h1,show (Finset.range 4={0,1,2,3}) by rfl]
    simp only [Finset.mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, Finset.mem_singleton, or_self,not_false_eq_true, Finset.sum_insert, OfNat.one_ne_ofNat, Nat.reduceEqDiff,Finset.sum_singleton]
    ring
  replace h2:a 0+a 1 +a 2+a 3 +a 4=1492:=by
    rw[←h2,show (Finset.range 5={0,1,2,3,4}) by rfl]
    simp only [Finset.mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, Finset.mem_singleton, or_self,not_false_eq_true, Finset.sum_insert, OfNat.one_ne_ofNat, Nat.reduceEqDiff,Finset.sum_singleton]
    ring
  suffices a 0 +a 1 +a 2=986 by
    rw[←this,show (Finset.range 3={0,1,2}) by rfl]
    simp only [Finset.mem_insert, zero_ne_one, Finset.mem_singleton, OfNat.zero_ne_ofNat, or_self,not_false_eq_true, Finset.sum_insert, OfNat.one_ne_ofNat, Finset.sum_singleton]
    ring
--Finally, we solve the linear equations.
  linarith