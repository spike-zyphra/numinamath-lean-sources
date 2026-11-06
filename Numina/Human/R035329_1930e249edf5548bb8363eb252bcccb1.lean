import Mathlib

abbrev Zpos := { x : ℕ | x > 0 }

/- Find all functions $\mathrm{f}$ on the positive integers with positive integer values such that (1) if $\mathrm{x}<\mathrm{y}$, then $f(x)<f(y)$, and $(2) f(y f(x))=x^{2} f(x y)$. -/
theorem algebra_604541 :
  { f : Zpos → Zpos | (∀ x y : Zpos, x < y → f x < f y) ∧ (∀ x y : Zpos, f ⟨y * f x, Set.mem_setOf.mpr (mul_pos y.2 (f x).2)⟩ = x ^ 2 * (f ⟨x * y, Set.mem_setOf.mpr (mul_pos x.2 y.2)⟩).1) } = { fun ⟨x, hx⟩ ↦ ⟨x ^ 2, Nat.pos_pow_of_pos 2 hx⟩} := by
  ext f
  constructor
  -- We first verify that x ↦ x^2 is a solution.
  swap
  . rintro rfl
    simp
    constructor
    . intro x hx y hy hxy
      exact Nat.pow_lt_pow_left hxy (by simp)
    . intro x hx y hy
      ring
  -- Now let f satisfy the given conditions.
  . rintro ⟨hf1, hf2⟩
    ext ⟨x, hx⟩
    simp at *
    -- We first show that f is injective.
    -- It follows clearly from (1).
    have finj x (hx : x > 0) y (hy : y > 0) (hxy : f ⟨x, hx⟩ = f ⟨y, hy⟩) : x = y := by
      have h₁ := hf1 x hx y hy
      have h₂ := hf1 y hy x hx
      apply mt at h₁
      apply mt at h₂
      push_neg at h₁ h₂
      specialize h₁ (le_of_eq hxy.symm)
      specialize h₂ (le_of_eq hxy)
      exact Nat.le_antisymm h₂ h₁
    -- Setting y = 1, we get f(f(x)) = x^2 f(x).  (3)
    have H₁ x (hx : x > 0) := hf2 x hx 1 (by simp)
    simp at H₁
    -- We now show that f(x * y) = f(x) * f(y).
    have H₂ x (hx : x > 0) z (hz : z > 0) : f ⟨x * z, mul_pos hx hz⟩ = (f ⟨x, hx⟩).1 * (f ⟨z, hz⟩).1 := by
      -- It suffices to show that f(f(x) * f(z)) = f(x * z).
      refine finj _ (f _).2 _ (mul_pos (f _).2 (f _).2) (Eq.symm (Subtype.eq ?_))
      calc
        -- = z ^ 2 * f(z * f(x)) from (2)
        _ = z ^ 2 * f ⟨z * f ⟨x, hx⟩, mul_pos hz (f _).2⟩ := hf2 z hz (f ⟨x, hx⟩) (f ⟨x, hx⟩).2
        -- = z ^ 2 * (x ^ 2 * f (x * z)) from (2)
        _ = z ^ 2 * (x ^ 2 * f ⟨x * z, mul_pos hx hz⟩) := by congr 1; exact hf2 x hx z hz
        -- = (x * z) ^ 2 * f (x * z)
        _ = (x * z) ^ 2 * f ⟨x * z, mul_pos hx hz⟩ := by ring
        -- = f (f (x * z)) from (3)
        _ = f ⟨f ⟨x * z, mul_pos hx hz⟩, (f _).2⟩ := (H₁ (x * z) (mul_pos hx hz)).symm
    -- Specifically, we have f(x^2) = (f(x))^2.  (4)
    have H₃ x (hx : x > 0) := H₂ x hx x hx
    simp [← sq] at H₃
    -- Now we show that f(x) = x^2 for all x.
    -- If otherwise, then we have f(x) < x^2 or f(x) > x^2 for some x.
    by_contra H
    apply lt_or_gt_of_ne at H
    rcases H with H | H
    . -- If f(x) < x^2 for some x, then we have f(f(x)) < f(x^2) from (1).
      have K := hf1 (f ⟨x, hx⟩) (f _).2 (x ^ 2) (Nat.pos_pow_of_pos 2 hx) H
      change (f (f ⟨x, hx⟩)).1 < (f ⟨x ^ 2, Nat.pos_pow_of_pos 2 hx⟩).1 at K
      -- Rewrite using (3) and (4), and we get x^2 * f(x) < f(x)^2.
      rw [H₁ x hx, H₃ x hx] at K
      nth_rw 2 [sq] at K
      -- Cancel f(x) from both sides, and we get x^2 < f(x).
      apply Nat.lt_of_mul_lt_mul_right at K
      -- That contradicts f(x) < x^2.
      exact Nat.lt_irrefl _ (H.trans K)
    . -- The same argument shows that f(x) > x^2 for some x leads to a contradiction.
      have K := hf1 (x ^ 2) (Nat.pos_pow_of_pos 2 hx) (f ⟨x, hx⟩) (f _).2 H
      change (f ⟨x ^ 2, Nat.pos_pow_of_pos 2 hx⟩).1 < (f (f ⟨x, hx⟩)).1 at K
      rw [H₁ x hx, H₃ x hx] at K
      nth_rw 1 [sq] at K
      apply Nat.lt_of_mul_lt_mul_right at K
      exact Nat.lt_irrefl _ (H.trans K)
