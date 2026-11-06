import Mathlib

open Finset

/- $37 \cdot 12$ In the Cartesian coordinate system, points with both coordinates being integers are called integer points. The number of integer points $(x, y)$ that satisfy the inequality $(|x|-1)^{2}+(|y|-1)^{2}<2$ is
(A) 16.
(B) 17.
(C) 18.
(D) 25.
(China High School Mathematics League, 1999) -/
theorem inequalities_292139 : Set.encard {(x, y) : ℤ × ℤ | (|x| - 1)^2 + (|y| - 1)^2 < 2} = 16 := by
  -- We show the set is contained in the square `[-2, 2] × [-2, 2]`, so it is finite.
  have H₁ (x y : ℤ) (h : (|x| - 1)^2 + (|y| - 1)^2 < 2) : (-2 ≤ x ∧ x ≤ 2) ∧ -2 ≤ y ∧ y ≤ 2 := by
    have hx : |x| ≤ 2 := by nlinarith
    have hy : |y| ≤ 2 := by nlinarith
    simp [abs_le] at hx hy
    exact ⟨hx, hy⟩
  -- So we write it as a finite set.
  have H₂ : {(x, y) : ℤ × ℤ | (|x| - 1)^2 + (|y| - 1)^2 < 2} = (Icc (-2 : ℤ) 2 ×ˢ Icc (-2) 2).filter (fun (x, y) => (|x| - 1)^2 + (|y| - 1)^2 < 2) := by
    ext ⟨x, y⟩
    simp
    exact H₁ x y
  rw [H₂, Set.encard_coe_eq_coe_finsetCard]
  -- Now we can count the number of points using `native_decide`.
  native_decide
