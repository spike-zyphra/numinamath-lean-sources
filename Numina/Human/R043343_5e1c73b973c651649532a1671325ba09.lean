import Mathlib

/- Problem 4. Given a quadratic trinomial $g(x)$, which has exactly one root.
Find this root, if it is known that the polynomial $g(a x+b)+g(c x+d)$ $(a \neq c)$ also has exactly one root. -/

theorem algebra_200258 {g : ℝ → ℝ} {a b c d: ℝ} {A x0: ℝ} (hA: A ≠ 0)
(hg : ∀ x: ℝ, g x = A * (x - x0) ^ 2) (hac : a ≠ c)
(h: ∃! x, g (a * x + b) + g (c * x + d) = 0): x0 = (a * d - b * c) / (a - c) := by

    obtain ⟨x1,h⟩ := h
    rcases h with ⟨h1,h2⟩
    clear h2 -- in fact, we only need h1 to prove the fact
    have f1:= hg (a * x1 + b)
    have f2:= hg (c * x1 + d)
    simp [f1,f2] at h1
    rw [show A * (a * x1 + b - x0) ^ 2 + A * (c * x1 + d - x0) ^ 2
    = A * ((a * x1 + b - x0) ^ 2 + (c * x1 + d - x0) ^ 2) by ring] at h1
    simp [hA] at h1

    -- then we show both brackets are zero
    rw [add_eq_zero_iff_of_nonneg] at h1
    rcases h1 with ⟨l, r⟩
    rw [sq_eq_zero_iff] at l r
    have o: a - c ≠ 0 := by
        by_contra! no
        replace no: a = c := by
          linarith
        simp [no] at hac
    have hx1: x1 = (d - b) / (a - c) := by
      field_simp [hac]
      nlinarith
    simp [hx1] at l
    field_simp [hac]
    field_simp [hac] at l
    nlinarith
    . apply sq_nonneg
    . apply sq_nonneg
      