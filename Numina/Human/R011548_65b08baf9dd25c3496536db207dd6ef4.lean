import Mathlib

open Real Set
open scoped Real

/- Prove that if $A, B, C$ are the angles of a right-angled triangle, then $\sin A \sin B \sin (A-B)+\sin B \sin C \sin (B-C)+\sin C \sin A \sin (C-A)+\sin (A-B) \sin (B-C) \sin (C-A)=0$. -/
theorem algebra_255098 {A B C : Real} (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (hright : A = π / 2 ∨ B = π / 2 ∨ C = π / 2) :
  sin A * sin B * sin (A - B) + sin B * sin C * sin (B - C) +
  sin C * sin A * sin (C - A) + sin (A - B) * sin (B - C) * sin (C - A) = 0 := by
    -- The formula is cyclic, so without loss of generality we can set $A = 90^\circ$.
    wlog hright' : A = π / 2 with h
    · rcases hright with hAright | hBright | hCright
      · by_contra
        exact hright' hAright
      · have := h hB hC hA (by linarith) (by simp_all) hBright
        linarith
      · have := h hC hA hB (by linarith) (by simp_all) hCright
        linarith
    /-  Then $A = B + C$, which allows us to write the problem as
    $\sin (B + C) \sin B \sin C+ \sin B \sin C \sin (B-C)+\sin C \sin (B + C) \sin (C - B)+\sin C \sin (B-C) \sin B=0$. This equality clearly holds, since the terms cancel each other out.-/
    have hABC : A = B + C := by linarith
    subst hABC
    simp
    linarith