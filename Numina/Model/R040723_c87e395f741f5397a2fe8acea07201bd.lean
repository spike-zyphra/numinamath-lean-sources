import Mathlib

theorem algebra_293849 {f g : ℝ → ℝ} (hfg : ∀ x, g (f x) = x ∧ f (g x) = x)
    (hf : ∃ k : ℝ, ∃ h : ℝ → ℝ, (∀ x, f x = k * x + h x) ∧
      (∃ d : ℝ, d ≠ 0 ∧ ∀ x, h x = h (x + d))) :
    ∃ k : ℝ, ∃ h' : ℝ → ℝ, (∀ y, g y = k * y + h' y) ∧
      (∃ d' : ℝ, d' ≠ 0 ∧ ∀ y, h' y = h' (y + d')) := by

  rcases hf with ⟨k, h, hf_eq, ⟨d, hd_ne, h_periodic⟩⟩

  have h1 : k ≠ 0 := by
    by_contra hk
    have h2 : k = 0 := by linarith
    have h6 : f 0 = f d := by
      have h7 : f = h := by
        funext x
        rw [hf_eq x, h2]
        all_goals simp
      have h7' : f = h := h7
      have h8 : f 0 = h 0 := by
        simp [h7']
      have h9 : f d = h d := by
        simp [h7']
      have h10 : h 0 = h d := by
        have h11 : h 0 = h (0 + d) := by
          rw [h_periodic 0]
          all_goals simp
        have h12 : 0 + d = (d : ℝ) := by linarith
        rw [h12] at h11
        linarith
      linarith [h8, h9, h10]
    have h7 : g (f 0) = (0 : ℝ) := (hfg 0).1
    have h8 : g (f d) = (d : ℝ) := (hfg d).1
    have h9 : g (f 0) = g (f d) := by
      rw [h6]
    have h10 : (0 : ℝ) = (d : ℝ) := by
      linarith [h7, h8, h9]
    exfalso
    apply hd_ne
    linarith

  use (1 / k)
  use fun y => g y - (1 / k) * y
  constructor
  · -- Show that g y = k * y + h' y
    intro y
    field_simp [h1]
    <;> ring
  · -- Show that h' is periodic for some non-zero d'
    use k * d
    constructor
    · -- Show that the period is non-zero
      by_contra h_eq
      have h11 : k * d = (0 : ℝ) := by linarith [h_eq]
      have h12 : k = 0 ∨ d = 0 := by
        cases (mul_eq_zero.mp h11) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith
      cases h12 with
      | inl hk0 => 
        contradiction
      | inr hd0 => 
        contradiction
    · -- Show that h' is k * d periodic
      intro y
      have eq1 : g (y + k * d) = g y + d := by
        have eq2 : f (g y + d) = f (g y) + k * d := by
          have eq3 : f (g y + d) = k * (g y + d) + h (g y + d) := by
            rw [hf_eq]
          have eq4 : h (g y + d) = h (g y) := by
            have h14 : h (g y) = h (g y + d) := by
              specialize h_periodic (g y)
              linarith
            linarith
          have eq5 : f (g y) = k * g y + h (g y) := by
            rw [hf_eq]
          rw [eq3]
          rw [eq4] 
          linarith [eq5]
        have eq3' : f (g y + d) = y + k * d := by
          have eq4' : f (g y) = y := by
            have h15 := (hfg y).2
            linarith
          linarith [eq2, eq4']
        have eq4' : g (f (g y + d)) = g y + d := by 
          have h16 := (hfg (g y + d)).1
          linarith [h16]
        have eq5' : g (f (g y + d)) = g (y + k * d) := by
          rw [eq3']
        linarith [eq4', eq5']
      have eq2 : (g y - (1 / k) * y) = (g (y + k * d) - (1 / k) * (y + k * d)) := by
        rw [eq1]
        field_simp [h1]
        <;> ring
      simpa using eq2