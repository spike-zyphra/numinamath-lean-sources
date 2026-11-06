import Mathlib

theorem algebra_122185 {f : ℝ → ℝ} (hf1 : f 1 = 1)
    (hfx : ∀ x, f (x + 5) ≥ f x + 5 ∧ f (x + 1) ≤ f x + 1) :
    (f 2002 + 1 - 2002) = 1 := by

  have h1 : ∀ x, f (x + 5) ≥ f x + 5 := by
    intro x
    exact (hfx x).left
  -- extract $f(x+1) \leq f(x)+1$ from hfx
  have h2 : ∀ x, f (x + 1) ≤ f x + 1 := by
    intro x
    exact (hfx x).right

  -- Show f(x + 5) ≤ f(x) + 5
  have h3 : ∀ x, f (x + 5) ≤ f x + 5 := by
    intro x
    have h4 : f (x + 5) = f ((x + 4) + 1) := by ring_nf
    rw [h4]
    have h5 : f ((x + 4) + 1) ≤ f (x + 4) + 1 := h2 (x + 4)
    have h6 : f (x + 4) = f ((x + 3) + 1) := by ring_nf
    rw [h6] at h5
    have h7 : f ((x + 3) + 1) ≤ f (x + 3) + 1 := h2 (x + 3)
    have h8 : f (x + 3) = f ((x + 2) + 1) := by  ring_nf
    rw [h8] at h7
    have h9 : f ((x + 2) + 1) ≤ f (x + 2) + 1 := h2 (x + 2)
    have h10 : f (x + 2) = f ((x + 1) + 1) := by  ring_nf
    rw [h10] at h9
    have h11 : f ((x + 1) + 1) ≤ f (x + 1) + 1 := h2 (x + 1)
    have h12 : f (x + 1) ≤ f x + 1 := h2 x
    linarith

  -- Now $f(x + 5) = f(x) + 5$
  have h4 : ∀ x, f (x + 5) = f x + 5 := by
    intro x
    linarith [h1 x, h3 x]

  -- Show $f(x + 1) = f(x) + 1$
  have h5 : ∀ x, f (x + 1) = f x + 1 := by
    intro x
    have h6 : f (x + 5) = f x + 5 := h4 x
    have h7 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h2 (x + 4)
      ring_nf at h2 ⊢
      linarith
    have h8 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h2 (x + 3)
      ring_nf at h2 ⊢
      linarith
    have h9 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h2 (x + 2)
      ring_nf at h2 ⊢
      linarith
    have h10 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h2 (x + 1)
      ring_nf at h2 ⊢
      linarith
    have h11 : f (x + 1) ≤ f x + 1 := h2 x
    have eq1 : f (x + 5) = f (x + 4) + 1 := by linarith [h6, h7]
    have eq2 : f (x + 4) = f (x + 3) + 1 := by linarith [eq1, h8]
    have eq3 : f (x + 3) = f (x + 2) + 1 := by linarith [eq2, h9]
    have eq4 : f (x + 2) = f (x + 1) + 1 := by linarith [eq3, h10]
    linarith [eq4, h11]

  -- Show $f(x + n) = f(x) + n$ for $x \in \mathbb{R}, n \in \mathbb{N}$
  have h8 : ∀ (n : ℕ), f (1 + ↑n) = 1 + ↑n := by
    intro n
    induction n with
    | zero =>
      norm_num [hf1]
    | succ n ih =>
      have h9 : f (1 + ↑(n + 1)) = f (1 + ↑n + 1) := by
        simp at *
        <;> ring_nf
      have h10 : f (1 + ↑n + 1) = f (1 + ↑n) + 1 := by
        specialize h5 (1 + ↑n)
        simpa using h5
      rw [h9, h10, ih]
      all_goals norm_num
      <;> linarith

  have h9 : f 2002 = 2002 := by
    have h10 : f (1 + (2001 : ℕ)) = 1 + (2001 : ℕ) := h8 2001
    norm_num at h10 ⊢
    linarith
  linarith [h9]