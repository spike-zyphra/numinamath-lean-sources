import Mathlib
open Real

/-
  Suppose $p$ and $q$ are both real numbers, and $\sin \alpha$ and $\cos \alpha$
  are the two real roots of the equation $x^{2}+px+q=0$ with respect to $x$. Find the minimum value of $p+q$.
  The final answer is $ \boxed{-1} $
-/
theorem algebra_9043 (hf : f = λ (p q x : ℝ) => x ^ 2 + p * x + q) :
    let is_root (p q : ℝ) := ∃ α : ℝ, ∀ z, f p q z = 0 ↔ z = sin α ∨ z = cos α;
    IsLeast {t | ∃ p q, is_root p q ∧ p + q = t} (-1) := by

  -- prove the vieda formula
  have vieta (p q x y : ℝ) (hr : ∀ z, f p q z = 0 ↔ z = x ∨ z = y) : x + y = -p ∧ x * y = q := by
    have h1 : f p q x = 0 := by apply (hr x).mpr; simp
    have h2 : f p q y = 0 := by apply (hr y).mpr; simp
    simp [hf] at h1 h2
    have : x * x - (- p) * x + q = 0 := by rw [<-h1]; ring
    obtain ⟨y', ⟨hy1', ⟨hy2', hy3'⟩⟩⟩ := by apply vieta_formula_quadratic this
    have : y * y - (- p) * y + q = 0 := by rw [<-h2]; ring
    rw [<-hy3', <-hy2'] at this
    have : (y - x) * (y - y') = 0 := by rw [<-this]; ring
    simp at this
    by_cases h : y' = y
    · rw [h] at hy2' hy3'
      exact ⟨hy2', hy3'⟩
    · obtain h' : y' = x ∨ y' = y := by apply (hr y').mp; simp [hf]; rw [<-hy1']; ring
      simp [h] at h'
      have h : y - y' ≠ 0 := by exact sub_ne_zero_of_ne fun a ↦ h (Eq.symm a)
      simp [h] at this h'
      rw [<-h'] at this
      contradiction

  simp [IsLeast, lowerBounds]
  constructor
  · -- verify when p = -1, q = 0, p + q = -1
    use -1, 0
    simp [hf]
    -- show that sin 0, cos 0 is the solutions of x^2-x=0
    use 0
    simp
    intro z
    constructor
    · intro hz
      have : z * (z - 1) = 0 := by rw [<-hz]; ring
      simp at this
      rcases this with h | h
      · apply Or.inl h
      · have : z = 1 := by linarith
        apply Or.inr this
    · intro hz
      rcases hz with h | h
      all_goals simp [h]
  · -- show that p + q ≥ -1
    intro _ p q α h ht
    rw [<-ht]
    -- apply the vieta lemma
    obtain ⟨h1, h2⟩ := vieta p q (sin α) (cos α) h
    have : (-p) ^ 2 = 1 + 2 * q := by
      rw [<-h1, <-h2]; ring_nf;  rw [show (1 = sin α ^ 2 + cos α ^ 2) by simp only [sin_sq_add_cos_sq]]; ring
    have : p + q = 1/ 2 * (p + 1) ^ 2 - 1 := by linarith
    rw [this]
    have : (p + 1) ^ 2 ≥ 0 := by exact sq_nonneg (p + 1)
    calc
      1 / 2 * (p + 1) ^ 2 - 1 ≥ 1 / 2 * 0 - 1 := by rel [this]
      _ = -1 := by simp
