import Mathlib

theorem algebra_300558 (f : ℕ → ℝ) (hf : f 1998 = 46 ∧ f 2000 = 58 ∧ f 2002 = 75)
    (h : ∃ a b c, ∀ x, f x = a * x ^ 2 + b * x + c) :
    f 2004 = 97 := by
        rcases hf with ⟨h1998, h2000, h2002⟩
        rcases h with ⟨a, b, c, h_eq⟩
        have eq1 : f 1998 = a * 1998 ^ 2 + b * 1998 + c := h_eq 1998
        have eq2 : f 2000 = a * 2000 ^ 2 + b * 2000 + c := h_eq 2000
        have eq3 : f 2002 = a * 2002 ^ 2 + b * 2002 + c := h_eq 2002
        have eq4 : f 2004 = a * 2004 ^ 2 + b * 2004 + c := h_eq 2004
        rw [h1998] at eq1
        rw [h2000] at eq2
        rw [h2002] at eq3
        norm_num at eq1 eq2 eq3 eq4
        linarith