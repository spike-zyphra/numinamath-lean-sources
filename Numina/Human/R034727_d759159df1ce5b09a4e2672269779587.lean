import Mathlib

/- 2. If the functions $f(x)$ and $g(x)$ are defined on $\mathbf{R}$, and $f(x-y)=f(x) g(y)-$ $g(x) f(y), f(-2)=f(1) \neq 0$, then $g(1)+g(-1)=$ $\qquad$ -/
theorem algebra_257089 {f g : ℝ → ℝ} (hfg : ∀ x y, f (x - y) = f x * g y - g x * f y)
    (hf : f (-2) = f 1) (hf' : f 1 ≠ 0) : g 1 + g (-1) = -1 := by

        --Show that f (y - x) = -f (x - y).
        have h1: ∀ x y, f (y - x) = - f (x - y) := by
            intro x y
            have h11 : f (y - x) = f y * g x - g y * f x := by
                --Here we use `hfg`.
                specialize hfg y x
                exact hfg
            have h12 : f (x - y) = f x * g y - g x * f y := by
                --Here we use `hfg`.
                specialize hfg x y
                exact hfg
            --Simplify.
            have h13 : f y * g x - g y * f x = - (f x * g y - g x * f y) := by
                ring
            rw [h13] at h11
            rw [← h12] at h11
            exact h11

        --Next, show that f (-2) = f (-1 -1).
        have h2 : f (-2) = f (-1 - 1) := by ring_nf

        --Show f (-1) = - f 1 using `h1`.
        have h3 : f (-1) = - f 1 := by
            calc
                _ = f (0 - 1) := by ring_nf
                _ = - f (1 - 0) := by
                    specialize h1 0 1; linarith
                _ = - f 1 := by ring_nf

        --Use `hfg` to show f (-1 - 1) = f (-1) * g 1 - g (-1) * f 1.
        have h4 : f (-1 - 1) = f (-1) * g 1 - g (-1) * f 1 := by
            specialize hfg (-1) 1
            exact hfg

        --Use `h3` to show  f (-1) * g 1 - g (-1) * f 1 = - f 1 * g 1 - g (-1) * f 1.
        have h5 : f (-1) * g 1 - g (-1) * f 1 = - f 1 * g 1 - g (-1) * f 1 := by
            rw [h3]

        --Simplify.
        have h6 : - f 1 * g 1 - g (-1) * f 1 = - f 1 * (g 1 + g (-1)) := by
            ring

        --Factor our - f(1).
        have h7 : f (-2) = - f 1 * (g 1 + g (-1)) := by
            linarith

        --Use the fact that f(1) = f(-2).
        have h8 : f 1 = - f 1 * (g 1 + g (-1)) := by
            linarith

        --Factor our f(1)
        have h9 : f 1 * (1 + g 1 + g (-1)) = 0 := by
            linarith

        --Cancel out f(1) using hf'.
        have h10 : 1 + g 1 + g (-1) = 0 := by
            exact (mul_eq_zero_iff_left hf').mp h9

        --Now `linarith` closes the goal.
        linarith