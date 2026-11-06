import Mathlib
/-Compute the number of sequences of numbers $a_{1}, a_{2}, \ldots, a_{10}$ such that

$$
\begin{aligned}
& \text { I. } a_{i}=0 \text { or } 1 \text { for all } i \\
& \text { II. } a_{i} \cdot a_{i+1}=0 \text { for } i=1,2, \ldots, 9 \\
& \text { III. } a_{i} \cdot a_{i+2}=0 \text { for } i=1,2, \ldots, 8
\end{aligned}
$$-/

open Finset

def isGood (a : Fin 10 → Fin 2) : Prop :=
  (∀ i ∈ Icc 1 9, a i * a (i + 1) = 0) ∧
  (∀ i ∈ Icc 1 8, a i * a (i + 2) = 0)

def A : ℕ → ℕ
| 0 => 2
| 1 => 3
| 2 => 4
| n + 3 => A (n + 2) + A n

instance :   Fintype ↑{a | isGood a} := by 
  simp[isGood]
  infer_instance

theorem combinatorics_608176 :
    {a | isGood a}.toFinset.card = A 9 := by
  simp [isGood, A]
  native_decide
 