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
  use [4, 5]
  use [3, 8]
  use [6, 7]
  constructor
  · -- Show that the concatenation is a permutation of [3, 4, 5, 6, 7, 8]
    native_decide
  constructor
  · -- Show that ethan's list length is 2
    simp
  constructor
  · -- Show that jacob's list length is 2
    simp
  constructor
  · -- Show that karthik's list length is 2
    simp
  constructor
  · -- Show that ethan's list product is 20
    all_goals native_decide
  constructor
  · -- Show that jacob's list product is 24
    all_goals native_decide
  · -- Show that karthik's list product is 42
    all_goals native_decide