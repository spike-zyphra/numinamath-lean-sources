import Mathlib

/- Let $k \geqslant 1$. Prove:(i)If $2^{k} \leqslant n<2^{k+1}$, and $1 \leqslant a \leqslant n, a \neq 2^{k}$, then $2^{k} \nmid a$;(ii)If $3^{k}\leqslant 2 n-1<3^{k+1},1\leqslantl\leqslantn, 2l-1 \neq 3^{k}$,then $3^{k}\nmid2l-1$.-/
theorem number_theory_5461 (_ : k ≥ 1) :
    (2 ^ k ≤ n ∧ n < 2 ^ (k + 1) → 1 ≤ a ∧ a ≤ n ∧ a ≠ 2 ^ k → ¬ 2 ^ k ∣ a) ∧ 
    (3 ^ k ≤ 2 * n - 1 ∧ 2 * n - 1 < 3 ^ (k + 1) → 1 ≤ l ∧ l ≤ n ∧ 2 * l - 1 ≠ 3 ^ k → ¬ 3 ^ k ∣ 2 * l - 1) := by
  constructor
  · -- First case: Proving the statement for powers of 2
    intro hn ha
    by_contra w
    -- Assume, for the sake of contradiction, that 2 ^ k divides a
    obtain ⟨t, ht⟩ := w
    -- Show that t must be less than 2
    have t1 : 2 ^ k * t < 2 ^ (k + 1) := by
      rw [← ht]
      omega
    rw [pow_add] at t1
    simp at t1
    -- Since t is a natural number, it can only be 0 or 1
    have t2 : t = 0 ∨ t = 1 := by
      omega
    cases t2
    <;> simp_all
  · -- Second case: Proving the statement for powers of 3
    intro hl hk
    by_contra w
    -- Assume, for the sake of contradiction, that 3^k divides 2 * l - 1
    obtain ⟨t, ht⟩ := w
    -- Show that 2*l-1 is less than or equal to 2*n-1
    have t0 : 2 * l - 1 ≤ 2 * n - 1 := by
      refine Nat.sub_le_sub_right ?_ 1
      omega
    -- Show that t must be less than 3
    have t1 : 3 ^ k * t < 3 ^ (k + 1) := by 
      rw [← ht]
      omega
    rw [pow_add] at t1
    simp at t1
    -- Since t is a natural number, it can only be 0, 1, or 2
    have t2 : t = 0 ∨ t = 1 ∨ t = 2 := by
      omega
    cases t2
    -- Handle the case where t = 2
    case right.intro.inl H =>
      simp [H] at ht
      omega
    -- Handle the cases where t = 0 or t = 1
    case right.intro.inr H =>
      cases H
      case inl H1 =>
        simp_all
      case inr H1 =>
        simp_all
        -- Show that 2 * l - 1 is odd, leading to a contradiction since 3 ^ k is odd
        have r : Odd (2 * l - 1) := by
          refine Nat.Even.sub_odd ?_ ?_ ?_ 
          omega
          exact even_two_mul l   
          trivial
        simp_all
        revert r
        simp
