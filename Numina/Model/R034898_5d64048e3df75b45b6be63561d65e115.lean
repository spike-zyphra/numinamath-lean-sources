import Mathlib

theorem algebra_5468 {f g : Polynomial ℤ} (hf : ∃ a b c d e : ℤ, f = a * (X + b) * (X + c) ∧
    g = d * (X + b) * (X + e)) (hfg : ∃ x : ℤ, f.eval x = 0 ∧ g.eval x = 0)
    (hb : b < 0) (hc : c < 0) (he : e < 0) :
    ¬∃ x : ℤ, x > 0 ∧ f.eval x = 20 ∧ g.eval x = 17 := by
  rcases hf with ⟨a, b, c, d, e, hf, hg⟩
  rcases hfg with ⟨x0, hfx0, hgx0⟩
  simp [hf] at hfx0
  simp [hg] at hgx0
  intro h
  rcases h with ⟨x, hx_pos, hfx, hgx⟩
  simp [hf] at hfx
  simp [hg] at hgx
  nlinarith [show b < 0 by linarith, show c < 0 by linarith, show e < 0 by linarith, sq_nonneg (x + b), sq_nonneg (x + e),
          sq_nonneg (x + c), sq_nonneg (x0 + b), sq_nonneg (x0 + c), sq_nonneg (x0 + e)]