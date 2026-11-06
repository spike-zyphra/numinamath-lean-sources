import Mathlib

/-Les Xantiens sont les habitants, en nombre éventuellement infini, de la planète Xanta. Vis-à-vis d'eux-mêmes et de leurs semblables, les Xantiens sont capables de ressentir deux types d'émotions, qu'ils appellent amour et respect. Il a été observé que:
- Chaque Xantien aime un et un seul Xantien, et respecte un et un seul Xantien.
- Si $A$ aime $B$, alors tout Xantien qui respecte $A$ aime également $B$.
- Si $A$ respecte $B$, alors tout Xantien qui aime $A$ respecte également $B$.
- Chaque Xantien est aimé d'au moins un Xantien.
Est-il vrai que chaque Xantien respecte le Xantien qu'il aime?-/
theorem logic_and_puzzles_607598 (X : Type) [Infinite X]
    (f g : X → X)
    (h1 : ∀ a b : X, f a = b → ∀ c, g c = a → f c = b)
    (h2 : ∀ a b : X, g a = b → ∀ c, f c = a → g c = b)
    (h3 : Function.Surjective f) :
    ∀ x : X, f x = g x := by
  -- Goal: Prove forall $x$, $f x = g x$.
  intro x
  -- Derive $f(g(x)) = f(x)$.
  have hfg : f (g x) = f x := by
    specialize h1 (g x) (f (g x)) rfl x rfl
    exact h1.symm
  -- Derive $g(f(x)) = g(x)$.
  have hgf : g (f x) = g x := by
    specialize h2 (f x) (g (f x)) rfl x rfl
    exact h2.symm
  -- Use surjectivity of f to find $y$ such that $f(y) = x$.
  have hsurj : ∃ y, f y = x := by
    apply h3
  obtain ⟨y, hy⟩ : ∃ y, f y = x := hsurj
  -- Prove $f x = x$.
  have hfx : f x = x := by
    have h5 : f (f y) = f y := by
      have h6 : f (g (f y)) = f (f y) := by
        specialize h1 (g (f y)) (f (g (f y))) rfl (f y) rfl
        exact h1.symm
      have h7 : g (f y) = g y := by
        specialize h2 (f y) (g (f y)) rfl y rfl
        exact h2.symm
      rw [h7] at h6
      have h8 : f (g y) = f y := by
        specialize h1 (g y) (f (g y)) rfl y rfl
        exact h1.symm
      rw [h8] at h6
      exact h6.symm
    have h9 : f y = x := hy
    rw [h9] at h5
    have h10 : f x = x := by
      simpa [h9] using h5
    exact h10
  -- Prove $g x = x$.
  have hgx : g x = x := by
    rw [hfx] at hfg
    have hfid : ∀ z, f z = z := by
      intro z
      obtain ⟨w, hw⟩ : ∃ w, f w = z := h3 z
      have hffw : f (f w) = f w := by
        have hfgfw : f (g (f w)) = f (f w) := by
          specialize h1 (g (f w)) (f (g (f w))) rfl (f w) rfl
          exact h1.symm
        have hgf : g (f w) = g w := by
          specialize h2 (f w) (g (f w)) rfl w rfl
          exact h2.symm
        rw [hgf, ←h1 (g w) (f (g w)) rfl w rfl] at hfgfw
        exact hfgfw.symm
      rw [hw] at hffw
      exact hffw
    rw [hfid] at hfg
    exact hfg
  -- Combine the two equations,derive $f x = g x$.
  rw [hfx, hgx]
