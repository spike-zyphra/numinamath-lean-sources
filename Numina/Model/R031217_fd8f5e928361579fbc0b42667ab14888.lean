import Mathlib

theorem algebra_254665 :
  { (p, q) : ℝ × ℝ | ∀ x : ℝ, (x^2 - 6 * x + 5) ∣ (x^4 + p * x^2 + q) } =
  { (-26, 25) } := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, if h holds, then ⟨p, q⟩ = ⟨-26, 25⟩.
    intro h
    have h1 := h 1
    have h5 := h 5
    norm_num at h1 h5
    have eq1 : p + q = -1 := by
      nlinarith
    have eq2 : 25 * p + q = -625 := by
      nlinarith
    have hp : p = -26 := by 
      nlinarith [eq1, eq2]
    have hq : q = 25 := by
      nlinarith [eq1, hp]
    simp [Prod.ext_iff, hp, hq]
    all_goals try { tauto }
  · -- Now, the reverse direction. If ⟨p, q⟩ = ⟨-26, 25⟩, then h holds.
    rintro ⟨rfl, rfl⟩
    intro x
    use x^2 + 6 * x + 5
    ring_nf