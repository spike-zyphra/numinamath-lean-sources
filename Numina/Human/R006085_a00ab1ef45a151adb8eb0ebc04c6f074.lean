import Mathlib 
open Finset
/-Find the number of solutions in positive integers $\left(k ; a_{1}, a_{2}, \ldots, a_{k} ; b_{1}, b_{2}, \ldots, b_{k}\right)$ to the equation

$$
a_{1}\left(b_{1}\right)+a_{2}\left(b_{1}+b_{2}\right)+\cdots+a_{k}\left(b_{1}+b_{2}+\cdots+b_{k}\right)=7 .
$$-/

def equation_sum (a b : List ℕ) : ℕ :=
  if a.length = b.length then
    let b_prefix_sums := (b.inits.tail).map List.sum
    ((a.zip b_prefix_sums).map (fun (x, y) => x * y)).sum
  else 0

structure MySolution where
  k : ℕ
  a : List ℕ
  b : List ℕ
deriving DecidableEq 

def IsValidSolution (sol : MySolution) : Prop :=
  sol.k > 0 ∧
  sol.a.length = sol.k ∧
  sol.b.length = sol.k ∧
  sol.a.all (· > 0) ∧
  sol.b.all (· > 0) ∧
  equation_sum sol.a sol.b = 7
instance :  DecidablePred IsValidSolution := by 
  unfold IsValidSolution equation_sum
  simp
  infer_instance


def solutions : Finset MySolution :=
  let vals := Finset.Icc 1 7

  -- Case k=1
  let k1_candidates := (Finset.product vals vals).map ⟨fun (i,j) => { k := 1, a := [i], b := [j] }, by simp[Function.Injective]⟩
  let k1_sols := k1_candidates.filter IsValidSolution

  -- Case k=2
  let k2_candidates := (Finset.product (Finset.product vals vals) (Finset.product vals vals))
    |>.map ⟨fun ((a₁,a₂),(b₁,b₂)) => { k := 2, a := [a₁,a₂], b := [b₁,b₂] }, by simp[Function.Injective]; simp_all⟩
  let k2_sols := k2_candidates.filter IsValidSolution

  -- Case k=3
  let k3_candidates := (Finset.product (Finset.product (Finset.product vals vals) vals) (Finset.product (Finset.product vals vals) vals))
    |>.map ⟨fun (((a₁,a₂),a₃),((b₁,b₂),b₃)) => { k := 3, a := [a₁,a₂,a₃], b := [b₁,b₂,b₃] }, by simp[Function.Injective]; simp_all⟩
  let k3_sols := k3_candidates.filter IsValidSolution

  k1_sols ∪ k2_sols ∪ k3_sols

theorem combinatorics_611480 : solutions.card = 15 := by
  native_decide