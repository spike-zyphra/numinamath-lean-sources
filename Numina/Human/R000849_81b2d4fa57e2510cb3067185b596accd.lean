import Mathlib

/-If 4 daps = 7 yaps, and 5 yaps = 3 baps, how many daps equal 42 baps?-/

theorem algebra_18587 (daps yaps baps : ℝ  ) (h : daps ≠ 0 ∧ yaps ≠ 0 ∧ baps ≠ 0) (h₀ : 4 * daps = 7 * yaps) (h₁ : 5 * yaps = 3 * baps)

    (h₂ : 42 * baps = x * daps) : x = 40 := by
    --Multiply $5\text{ yaps}=3\text{ baps}$ by 14 to find that 70 yaps are equal to 42 baps.  Then multiply $4\text{ daps}=7\text{ yaps}$ by 10 to find that $\boxed{40}$ daps are equal to 70 yaps.
    have e := congrArg ( fun (t) => (t)  / 3) h₁; simp at e; ring_nf at e
    have e2 := congrArg ( fun (t) => (t)  / 7) h₀; simp at e2; ring_nf at e
    rw[← e] at h₂
    rw[← e2] at h₂
    have e3 := congrArg ( fun (t) => (t:ℝ)  / (daps)) h₂; beta_reduce at e3;
    have eq : (42:ℝ ) * (4 * ↑daps / 7 * (5 / 3)) / ↑daps = 42* (4  * 5  /(7 *3 )) *(↑daps/↑daps) := by
      ring_nf
    rw [eq] at e3
    rw [show x * daps / daps = x * (daps / daps) by ring_nf] at e3
    rcases h with ⟨hd,⟨_,_⟩⟩
    have eq2 : ↑daps / (↑daps) = 1  := by
      apply div_self hd
    rw [eq2] at e3
    ring_nf at e3
    symm at e3
    exact e3
