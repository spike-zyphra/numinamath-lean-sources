import Mathlib

theorem algebra_294182 {f : ℝ → ℝ} (h₁ : ∀ x, f (10 + x) = f (10 - x)) (h₂ : ∀ x, f (20 - x) = -f (20 + x)) :
    Odd f ∧ ∃ c, Function.Periodic f c := by
  have h4 : ∀ y, f (-y) = -f y := by
    intro y
    have eq1 : f (-y) = f (20 + y) := by
      have h11 := h₁ (-y - 10)
      have : 10 + (-y - 10) = -y := by ring
      rw [this] at h11
      have : 10 - (-y - 10) = (20 + y : ℝ) := by ring
      rw [this] at h11
      linarith
    have eq2 : f (20 + y) = -f y := by
      have h11 := h₁ (y - 10)
      have : 10 + (y - 10) = y := by ring
      rw [this] at h11
      have : 10 - (y - 10) = (20 - y : ℝ) := by ring
      rw [this] at h11
      have eq4 : f (20 - y) = -f (20 + y) := by
        have h22 := h₂ y
        ring_nf at h22 ⊢
        linarith
      rw [eq4] at h11
      linarith
    linarith [eq1, eq2]

  have oddf : Odd f := by
    unfold Odd
    use (fun x => (f x - 1) / 2)
    funext x
    simp
    have h_eq : f (-x) = -f x := h4 x
    linarith

  have h8 : ∀ x, f (x + 40) = f x := by
    intro x
    have eq4 : f (x + 20) = -f x := by
      have h11 := h₁ (x - 10)
      have : 10 + (x - 10) = x := by ring
      rw [this] at h11
      have : 10 - (x - 10) = (20 - x : ℝ) := by ring
      rw [this] at h11
      have eq4 : f (20 - x) = -f (20 + x) := by
        have h22 := h₂ x
        ring_nf at h22 ⊢
        linarith
      rw [eq4] at h11
      have eq5 : f (20 + x) = f (x + 20) := by ring_nf
      rw [eq5] at h11
      linarith
    have eq5 : f (x + 40) = f x := by
      have h11 : f (x + 20) = -f x := eq4
      have h22 : f (x + 40) = -f (x + 20) := by
        have : f (x + 20 + 20) = -f (x + 20) := by
          have h111 := h₁ ((x + 20) - 10)
          have : 10 + ((x + 20) - 10) = (x + 20) := by ring
          rw [this] at h111
          have : 10 - ((x + 20) - 10) = (20 - (x + 20) : ℝ) := by ring
          rw [this] at h111
          have eq4 : f (20 - (x + 20)) = -f (20 + (x + 20)) := by
            have h22 := h₂ (x + 20)
            ring_nf at h22 ⊢
            linarith
          rw [eq4] at h111
          have eq5 : f (20 + (x + 20)) = f (x + 20 + 20) := by ring_nf
          rw [eq5] at h111
          linarith
        ring_nf at this ⊢
        linarith
      linarith [h11, h22]
    exact eq5

  constructor
  · exact oddf
  · use 40
    unfold Function.Periodic
    intro x
    apply h8 x