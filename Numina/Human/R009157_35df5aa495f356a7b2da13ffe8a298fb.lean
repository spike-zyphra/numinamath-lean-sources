import Mathlib
/-Each pack of hot dogs contains 10 hot dogs (no buns), but each pack of hot dog buns contains 8 buns.  Phil buys a number of these packs for a barbecue.  After the barbecue, Phil finds that he has 4 hot dogs left over.  What is the SECOND smallest number of packs of hot dogs he could have bought?-/
theorem number_theory_15941 :6 ∈ {n | n * 10 % 8 = 4} ∧ {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6}.ncard = 1 := by
  constructor
  .
    simp
  .
    --Let $n$ be the number of packs of hot dogs that Phil bought.  Then $10n \equiv 4 \pmod{8}$, which reduces to $2n \equiv 4 \pmod{8}$.  This congruence tells us that $2n = 8k + 4$ for some integer $k$, or $n = 4k + 2$.  The second smallest positive integer of this form is $\boxed{6}$.
    have heq : {x | x ∈ {n | n * 10 % 8 = 4} ∧ x < 6} = {2} := by
      simp
      ext x
      constructor
      .
        simp
        intro hx hx2
        rw [← Finset.mem_range] at hx2
        fin_cases hx2
        any_goals simp; simp at hx
        rfl
      .
        simp
        intro hx
        rw [hx]; simp
    rw [heq]
    simp