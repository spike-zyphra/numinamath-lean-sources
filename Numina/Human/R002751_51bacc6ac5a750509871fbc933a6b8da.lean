import Mathlib

/- $1 \cdot 22$ Assembling products A, B, and C requires three types of parts, $A$, $B$, and $C$. Each product A requires 2 $A$s and 2 $B$s; each product B requires 1 $B$ and 1 $C$; each product C requires 2 $A$s and 1 $C$. Using the inventory of $A$, $B$, and $C$ parts, if $p$ units of product A, $q$ units of product B, and $r$ units of product C are assembled, then 2 $A$s and 1 $B$ are left over, but $C$ is exactly used up. Prove that no matter how the quantities of products A, B, and C are changed, it is impossible to use up all the inventory of $A$, $B$, and $C$ parts.
(China High School Mathematics League, 1981) -/
theorem algebra_108921 {A B C S: Multiset (Fin 3)}
  (hA : A = {0, 0, 1, 1})
  (hB : B = {1, 2})
  (hC : C = {0, 0, 2})
  (p q r : ℕ)
  (hS1 : p • A + q • B + r • C ≤ S)
  (hS2 : S - (p • A + q • B + r • C) = {0, 0, 1})
  : ¬(∃ s t u : ℕ, s • A + t • B + u • C = S) := by

    -- we assign scores to each part:
    -- part $A$ (0) gets a score of 1
    -- part $B$ (1) gets a score of 2
    -- part $C$ (2) gets a score of 4
    let f : Fin 3 → ℕ := ![1, 2, 4]

    -- each product has a total score of 6
    have A_sum : (A.map f).sum = 6 := by norm_num [hA, f]
    have B_sum : (B.map f).sum = 6 := by norm_num [hB, f]
    have C_sum : (C.map f).sum = 6 := by norm_num [hC, f]

    -- to show that there doesn't exist s t u such that both sides are
    -- equal, we show that every choice of s t u makes them un-equal
    simp only [not_exists]
    intro s t u

    -- We have an equality for the collection of all parts
    have S_eq : S = {0, 0, 1} + (p • A + q • B + r • C) := by
      apply_fun (· + (p • A + q • B + r • C)) at hS2
      convert hS2
      exact (tsub_add_cancel_of_le hS1).symm

    -- so we have an expression for the score of all parts
    have S_sum : (S.map f).sum % 6 = (({0, 0, 1} + (p • A + q • B + r • C)).map f).sum % 6 := by
      apply_fun (fun T => (T.map f).sum % 6) at S_eq
      exact S_eq

    -- but the LHS of that expression is equal to 4
    have rhs_eq : (({0, 0, 1} + (p • A + q • B + r • C)).map f).sum % 6 = 4 := by
      norm_num [Multiset.map_nsmul, Multiset.sum_nsmul, A_sum, B_sum, C_sum, f]
      convert_to (4 + 6 * (p + q + r)) % 6 = 4
      · omega
      rw [←Nat.mod_add_mod]
      norm_num

    -- so the total score of all parts is 4
    rw [rhs_eq] at S_sum

    -- But all choices have a total score of 0
    have choices_eq : ((s • A + t • B + u • C).map f).sum % 6 = 0 := by
      norm_num [Multiset.map_nsmul, Multiset.sum_nsmul, A_sum, B_sum, C_sum]

    -- so they can't be equal
    apply_fun (fun T => (T.map f).sum % 6)
    simp only [choices_eq, S_sum]
    linarith