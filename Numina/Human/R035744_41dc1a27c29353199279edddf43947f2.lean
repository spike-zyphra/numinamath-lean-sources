import Mathlib

/- For every positive integer $n$, let $
mod_5 (n)$ be the remainder obtained when $n$ is divided by $5$. Define a function $f: \mathbb{N} \times \{0, 1, 2, 3, 4\} \to \{0, 1, 2, 3, 4\}$ recursively as follows:
​
$f:\{0,1,2,3,\cdots\}\times\{0,1,2,3,4\}\rightarrow \{0,1,2,3,4\}$ recursively as follows:
\[
f(i,j)=\begin{cases}
​mod_5(j+1)& if\ i=0\ and\ 0\leq j\leq 4,\\
f(i−1,1)& if\ i\geq 1\ and\ j=0,\\
f(i−1,f(i,j−1))& if\ i\geq 1\ and\ 1\leq j\leq 4.
​
\end{cases}
​\]
What is $f(2015,2)$?
$(A)0(B)1(C)2(D)3(E)4$ -/
theorem number_theory_96796 (f : ℕ → ℕ → ℕ)
(h₀ : ∀ i j, i = 0 → j ≤ 4 → f i j = (j + 1)%5)
(h₁ : ∀ i j, i ≥ 1 → j = 0 → f i j = f (i - 1) 1)
(h₂ : ∀ i j, i ≥ 1 → 1 ≤ j ∧ j ≤ 4 → f i j = f (i - 1) (f i (j - 1))) :f 2015 2 = 1 := by
    have mainthm (i :ℕ) (hi:5≤ i):∀j, (jle4:j≤4) → f i j= 1:=by
--Now we claim that for all $i\geq 5$, $f(i,j)=1$ for all $j\leq 4$.
        induction' i,hi using Nat.le_induction with k kge5
--We prove this by using induction on $i$ with the induction hypothesis that for all $k\leq i$ and $k\geq 5$, $f(k,j)=1$ for all $j\leq 4$.
        · intro j jle4
          interval_cases j
          all_goals simp[h₁,h₂,h₀]
--For the base case, we have $f(5,j)=1$ for all $j\leq 4$ by calculation.
        · rename_i hk
          intro j jle4
--For the inductive steps, we prove by using induction on $j$.
          induction' j with l hl
          · rw[h₁,Nat.add_sub_cancel,hk]
--For the base case, we have $f(k+1,0)=f(k,1)=1$ by the condition and $f(k,1)=1$ by the induction hypothesis of $k$.
            norm_num;norm_num;rfl
          · rw[h₂,Nat.add_sub_cancel,Nat.add_sub_cancel,hl,hk]
--For the inductive steps, we have $f(k+1,l+1)=f(k,f(k+1,l))=f(k,1)=1$ by the induction hypothesis of $k$ and $l$.
            norm_num;linarith;norm_num;norm_num;exact jle4
    rw[mainthm]
--The answer is $f(2015,2)=1$ by our claim.
    norm_num;norm_num