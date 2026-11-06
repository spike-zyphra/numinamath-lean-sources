import Mathlib

open Polynomial

/-- Compute the sum of all the roots of
  (2x+3)(x−4)+(2x+3)(x−6)=0.
  (A) 72(B) 4(C) 5(D) 7(E) 13 -/
theorem algebra_93957 (P : Polynomial ℝ) (hP : P = (2 * X + 3) * (X - 4) + (2 * X + 3) * (X - 6)) :
    P.roots.sum = 7 / 2 := by
  -- The polynomial clearly equals 4(x - (-3/2))(x-5).
  have (x : ℝ) : P.eval x = 4 * (x - (-3/2)) * (x - 5) := by
    rw[hP]
    simp only [eval_add, eval_mul, eval_ofNat, eval_X, eval_sub]
    ring
  have ne0 : P ≠ 0 := by
    intro h
    have that := congrArg (fun P => P.eval 0) h
    specialize this 0
    dsimp at that
    rw[that] at this
    simp at this
  -- Hence, the roots are -3/2 and 5.
  have sub : {-3 / 2, 5} ≤ P.roots := by
    rw[Multiset.le_iff_subset]
    intro x hx
    fin_cases hx
    · rw[mem_roots ne0]
      specialize this (-3/2)
      simpa using this
    · rw[mem_roots ne0]
      specialize this 5
      simpa using this
    · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, and_true]
      norm_num
  have : {-3 / 2, 5} = P.roots := by
    have : P.natDegree = 2 := by rw[hP]; compute_degree!
    have card1 := this ▸ P.card_roots'
    have card2 : ({- 3 / 2 , 5} : Multiset ℝ).card = 2 := by simp
    apply Multiset.eq_of_le_of_card_le sub
    rwa[card2]
  rw[← this]
  -- Since none of them occur multiple times, their sum equals 7/2.
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  ring