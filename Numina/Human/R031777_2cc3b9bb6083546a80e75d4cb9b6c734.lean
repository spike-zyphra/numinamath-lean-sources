import Mathlib.Tactic

/-Six consecutive positive integers are written on slips of paper.
The slips are then handed out to Ethan, Jacob, and Karthik,
such that each of them receives two slips. The product of Ethan's numbers is 20,
and the product of Jacob's numbers is 24 .
 Compute the product of Karthik's numbers.-/
def six_consecutive : List ℕ := [3, 4, 5, 6, 7, 8]

theorem number_theory_610773 :
  ∃ (ethan jacob karthik : List ℕ),
    (ethan ++ jacob ++ karthik).Perm [3, 4, 5, 6, 7, 8] ∧
    ethan.length = 2 ∧ jacob.length = 2 ∧ karthik.length = 2 ∧
    ethan.prod = 20 ∧ jacob.prod = 24 ∧ karthik.prod = 42 := by
    -- We only need to show the existence of the problem, since the uniqueness is easy: --
    -- uniqueness: 20 = 4 * 5, 2 * 10, 1 * 20, only 4 * 5 is possible --
    use [4, 5], [3, 8], [6, 7]  -- Assign Ethan, Jacob, Karthik their pairs
    simp only [List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, List.append_assoc,
      List.cons_append, List.nil_append, List.Perm.cons, List.Perm.refl, and_self]
    constructor
    . native_decide
    . simp