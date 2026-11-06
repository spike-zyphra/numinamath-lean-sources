import Mathlib

/- Find the number of unordered pairs $\{a, b\}$, where $a, b \in\{0,1,2, \ldots, 108\}$ such that 109 divides $a^{3}+b^{3}-a b$. -/
theorem number_theory_609839 :
    let ls := List.filter (fun (a, b) => a ≤ b ∧ 109 ∣ (a^3 + b^3 : ℤ)- a*b) ((List.range 109).product (List.range 109));
    ls.length = 54 :=
by
  intros ls
  simp[ls]
  set_option maxRecDepth 10000 in rfl
