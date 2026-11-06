import Mathlib
open Real

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
  constructor
  · -- verify when p = -1, q = 0, p + q = -1
    use -1, 0
    simp [hf]
    use Real.pi / 2
    intro z
    simp [hf]
    constructor
    · intro h
      have h1 : z ^ 2 + -1 * z + 0 = 0 := by linarith
      have : z ^ 2 - z = 0 := by linarith
      have : z * (z - 1) = 0 := by linarith
      cases' (mul_eq_zero.mp this) with hz hz
      · right
        linarith
      · left
        linarith
    · rintro (h | h)
      · rw [h]
        ring
      · rw [h]
        ring
  · -- verify p + q >= -1
    rintro t ⟨p, q, ⟨α, hα⟩, hpq⟩
    obtain ⟨hp, hq⟩ := vieta p q (sin α) (cos α) hα
    have hp' : sin α + cos α = -p := by linarith
    have hq' : sin α * cos α = q := by linarith
    nlinarith [sq_nonneg (sin α + cos α - 1), sq_nonneg (sin α - cos α), Real.sin_sq_add_cos_sq α]