import Mathlib

theorem algebra_150089 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2) :
    ¬∃ g h : ℝ → ℝ, (∃ c > 0, Function.Periodic g c) ∧ (∃ c > 0, Function.Periodic h c) ∧
      ∀ x, f x = g x + h x := by
  rintro ⟨g, h, ⟨c, hc, hg⟩, ⟨d, hd, hh⟩, heq⟩
  have h1 : ∀ x, f x = g x + h x := heq
  have hg1 : ∀ x, g (x + c) = g x := by
    intro x
    exact hg x
  have hh1 : ∀ x, h (x + d) = h x := by
    intro x
    exact hh x
  have h2 := h1 0
  simp [hf] at h2
  have h3 := h1 c
  simp [hf] at h3
  have h4 : g c = g 0 := by
    specialize hg1 0
    norm_num at hg1 ⊢
    linarith
  have h5 : h d = h 0 := by
    specialize hh1 0
    norm_num at hh1 ⊢
    linarith
  have h6 := h1 d
  simp [hf] at h6
  have h7 := h1 (-d)
  simp [hf] at h7
  have h8 : h (-d) = h 0 := by
    specialize hh1 (-d)
    have : -d + d = (0 : ℝ) := by linarith
    rw [this] at hh1
    linarith
  have h9 := h1 (c + d)
  simp [hf] at h9
  have h10 : g (c + d) = g d := by
    have : c + d = d + c := by ring
    rw [this]
    have : g (d + c) = g d := by
      specialize hg1 d
      simpa using hg1
    linarith
  have h11 : h (c + d) = h c := by
    have : c + d = c + d := by ring
    have : h (c + d) = h c := by
      specialize hh1 c
      simpa using hh1
    linarith
  nlinarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hc, hd]