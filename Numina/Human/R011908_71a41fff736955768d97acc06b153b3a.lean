import Mathlib

open SignType

/- We show that the number of positive elements in a list is equal to the number of 1s in the list of signs. -/
def lemma_1 (l : List ℝ) : l.countP (· > 0) = (l.map sign).count 1 := by
  symm
  calc (l.map sign).count 1
    _ = (l.map sign).countP (· == 1) := rfl
    _ = l.countP ((· == 1) ∘ sign) := List.countP_map _ _ _
    _ = l.countP (· > 0) := by
      congr
      ext x
      simp only [beq_eq_decide, Function.comp_apply, sign_eq_one_iff, gt_iff_lt]

/- We show that the number of negative elements in a list is equal to the number of -1s in the list of signs. -/
def lemma_2 (l : List ℝ) : l.countP (· < 0) = (l.map sign).count (-1) := by
  symm
  calc (l.map sign).count (-1)
    _ = (l.map sign).countP (· == -1) := rfl
    _ = l.countP ((· == -1) ∘ sign) := List.countP_map _ _ _
    _ = l.countP (· < 0) := by
      congr
      ext x
      simp only [beq_eq_decide, Function.comp_apply, sign_eq_neg_one_iff]

/- We show that the sign of a non-zero real number is either -1 or 1. -/
def lemma_3 {x : ℝ} (hx : x ≠ 0) : sign x ∈ ({-1, 1} : Finset SignType) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases lt_or_gt_of_ne hx with hx' | hx'
  . left
    exact sign_neg hx'
  . right
    exact sign_pos hx'

/- 3. Let $a, b, c, d$ all be non-zero real numbers. Then $-ab$, $ac$, $bd$, $cd$ (   ).
(A) are all positive
(B) are all negative
(C) are two positive and two negative
(D) are one positive and three negative or one negative and three positive -/
theorem algebra_306887 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    List.countP (· > 0) [-a * b, a * c, b * d, c * d] = 1 ∧ List.countP (· < 0) [-a * b, a * c, b * d, c * d] = 3 ∨ List.countP (· > 0) [-a * b, a * c, b * d, c * d] = 3 ∧ List.countP (· < 0) [-a * b, a * c, b * d, c * d] = 1 := by
  -- We rewrite the goal in terms of signs.
  rw [lemma_1, lemma_2]
  -- We simplify the goal using sign(-x) = -sign(x) and sign(x * y) = sign(x) * sign(y).
  simp only [neg_mul, List.map_cons, Left.sign_neg, sign_mul, List.map_nil]
  -- We apply lemma 3 to the non-zero real numbers.
  apply lemma_3 at ha
  apply lemma_3 at hb
  apply lemma_3 at hc
  apply lemma_3 at hd
  -- We focus on the signs of the non-zero real numbers instead of the real numbers themselves.
  generalize sign a = sa at ha
  generalize sign b = sb at hb
  generalize sign c = sc at hc
  generalize sign d = sd at hd
  -- We consider the possible combinations of signs, there are only 16 cases.
  -- We can use `native_decide` to check all of them.
  revert sa sb sc sd
  native_decide
