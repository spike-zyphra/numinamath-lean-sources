import Mathlib

theorem algebra_218449 {f g : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (hg : ∃ d e f, g = fun x => d * x ^ 2 + e * x + f) (hfg : f (-3) = g (-3)) (hfg' : f (-3) > g (-3))
    (hfg'' : ∫ x in (-3)..0, |f x - g x| = 12) :
    ∫ x in (0)..4, |f x - g x| = 4 := by
        linarith [hfg, hfg']