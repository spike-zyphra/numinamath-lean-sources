import Mathlib

theorem algebra_10492 {f g : ℕ → ℕ} (hf : f 3 = 10 ∧ f 4 = 17 ∧ f 5 = 26 ∧ f 6 = 37 ∧ f 7 = 50)
    (hg : g 10 = 3 ∧ g 17 = 4 ∧ g 26 = 5 ∧ g 37 = 6 ∧ g 50 = 7) :
    g (g 50 * g 10 + g 26) = 5 := by
  rcases hf with ⟨h3, h4, h5, h6, h7⟩
  rcases hg with ⟨hg10, hg17, hg26, hg37, hg50⟩
  simp [hg10, hg17, hg26, hg37, hg50]