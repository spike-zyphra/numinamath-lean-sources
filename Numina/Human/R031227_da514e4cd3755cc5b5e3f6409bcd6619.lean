import Mathlib

open Real Set
open scoped Real

/- 5. For any $\varphi \in\left(0, \frac{\pi}{2}\right)$, we have
(A) $\sin \sin \varphi>\cos \varphi>\cos \cos \varphi$;
(C) $\sin \cos \varphi>\cos \varphi>\cos \sin \varphi$;
(D) $\sin \cos \varphi<\cos \varphi<\cos \sin \varphi$. -/
theorem inequalities_211803 (φ : Real) (hφ : φ ∈ Ioo 0 (π/2)) :
    sin (cos φ) < cos φ ∧ cos φ < cos (sin φ) := by
  simp at hφ
  and_intros
  -- first inequlaity 0 < cos φ due to φ's range and so sin x < x proves goal
  . have : 0 < cos φ := by
      refine cos_pos_of_mem_Ioo ?_
      and_intros <;> linarith
    exact sin_lt this
  -- second goal, sin φ < φ as 0 < φ, then due to cos being antitone on [-π/2, π/2], goal is proved
  . have : sin φ < φ := by apply sin_lt (by linarith)
    apply strictAntiOn_cos
    . and_intros
      . apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
      . linarith
    . and_intros <;> linarith
    . assumption