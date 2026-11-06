import Mathlib

/- Which of the following values is largest?
(A) 2+0+1+7   (B) 2×0+1+7   (C) 2+0×1+7   (D) 2+0+1×7   (E) 2×0×1×7 -/
theorem algebra_93021 : (2 + 0 + 1 + 7) > (2 * 0 + 1 + 7) ∧
(2 + 0 + 1 + 7) > (2 + 0 * 1 + 7) ∧ 
(2 + 0 + 1 + 7) > (2 + 0 + 1 * 7) ∧
(2 + 0 + 1 + 7) > (2 * 0 * 1 * 7) := by
--compare case by case the first answer with the others to see it is the biggest.
constructor <;> simp