import Mathlib

-- Compute $$ \sum_{n_{60}=0}^{2} \sum_{n_{59}=0}^{n_{60}} \cdots \sum_{n_{2}=0}^{n_{3}} \sum_{n_{1}=0}^{n_{2}} \sum_{n_{0}=0}^{n_{1}} 1 $$
theorem combinatorics_611445 :
  let compute (count : ℕ) : ℕ → ℕ :=
    Nat.recAux
        (fun preN => preN + 1)
        (fun _ cmpN preN => List.sum (.map (cmpN) (.range (preN + 1))))
        count
  (compute 60 2 = 1953) :=
by
  intro compute
  simp[compute]
  set_option maxRecDepth 800 in rfl
