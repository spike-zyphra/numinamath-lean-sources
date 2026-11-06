import Mathlib

theorem algebra_13253 {k : ℝ} (f g h : ℝ → ℝ)
    (hf : f = fun x => x^3 + (k - 1)*x^2 + (3*k - 4)*x - 5*k)
    (hg : g = fun x => x^3 + (k + 1)*x^2 + (5*k - 1)*x + (3 - k))
    (hh : h = fun x => x^3 + k*x^2 + (4*k - 6)*x - 3*k)
    (hfg : ∃ x, f x = g x ∧ g x = h x) :
    k = -51/77 := by
  rcases hfg with ⟨x, hfx_gx, hgx_hx⟩
  simp [hf, hg, hh] at hfx_gx hgx_hx
  ring_nf at hfx_gx
  ring_nf at hgx_hx
  nlinarith [sq_nonneg (x + 3 / 7), sq_nonneg (x - (-3 / 7)), sq_nonneg (x + 1)]