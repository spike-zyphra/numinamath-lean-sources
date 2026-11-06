import Mathlib

/- You have linear functions $p(x)$ and $q(x)$. You know $p(2)=3$, and $p(q(x))=4x+7$ for all $x$. Find $q(-1)$. -/
theorem algebra_20569 {p q : ℝ → ℝ} (hp : ∃ a b, p = fun x => a * x + b)
    (hq : ∃ c d, q = fun x => c * x + d) (h2 : p 2 = 3) (h : ∀ x, p (q x) = 4 * x + 7) :
    q (-1) = 2 := by
    -- introduce a, b
    rcases hp with ⟨a, ⟨b, hp⟩⟩
    -- prove a ≠ 0, otherwise p is constant
    have ha : a ≠ 0 := by
        intro ha0
        rw [ha0] at hp
        simp at hp
        rw [hp] at h2 h
        simp at h2
        rw [h2] at h
        simp at h
        specialize h 0
        linarith
    -- specialize h (-1) to have q (-1)
    specialize h (-1)
    -- simplify p (q (-1)) = 4 * (-1) + 7
    rw [hp] at h h2
    simp at h h2
    have hb : b = - a * 2 + 3 := by linarith
    rw [hb] at h
    -- have a * (q (-1) - 2) = 0
    replace h : a * (q (-1) - 2) = 0 := by linarith
    -- then a = 0 or q (-1) - 2 = 0
    replace h : a = 0 ∨ q (-1) - 2 = 0 := mul_eq_zero.mp h
    -- discuss the two cases
    rcases h with ⟨ha0, hq⟩
    . contradiction -- a = 0 is a contradiction
    . linarith
