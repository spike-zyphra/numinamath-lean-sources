import Mathlib.Tactic

/-
PROBLEM:
Paula the painter had just enough paint for 30 identically sized rooms.  Unfortunately, on the way to work, three cans of paint fell off her truck, so she had only enough paint for 25 rooms.  How many cans of paint did she use for the 25 rooms?
$\mathrm{(A)}\ 10\qquad \mathrm{(B)}\ 12\qquad \mathrm{(C)}\ 15\qquad \mathrm{(D)}\ 18\qquad \mathrm{(E)}\ 25$
-/

theorem alg_1208
  (can room : ℕ)
  (three_cans_eq_five_rooms : (3 : ℚ) * can = 5 * room) :
  (15 : ℚ) * can = 25 * room := by
    -- Multiply both sides of the 3 cans to 5 rooms relation by 5
    have h : 5 * ((3 : ℚ) * can) = 5 * (5 * room) := by rw [three_cans_eq_five_rooms]
    -- Simplify
    rw [← mul_assoc, ← mul_assoc] at h
    norm_num at h
    exact h