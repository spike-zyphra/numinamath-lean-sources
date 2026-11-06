import Mathlib

open Real
theorem algebra_111734 {f : ℝ → ℝ} {x y}
    (hf : f = λ x => ((x + 1)^2 + sin x) / (x^2 + 1))
    (h : IsGreatest (Set.range f) x) (h' : IsLeast (Set.range f) y) :
    x + y = 2 := by
  have h1 : ∀ t, f t = ((t + 1) ^ 2 + sin t) / (t ^ 2 + 1) := by
    intro t
    rw [hf]

  have h2 : ∀ t, f (-t) + f t = 2 := by
    intro t
    rw [h1 (-t), h1 t]
    have h3 : sin (-t) = - sin t := by
      rw [sin_neg]
    simp only [h3]
    field_simp
    <;> ring_nf <;> simp [sin_sq]
    <;> ring

  have h3 : x ∈ Set.range f := h.1
  have h4 : ∀ r, r ∈ Set.range f → r ≤ x := h.2
  have h5 : y ∈ Set.range f := h'.1
  have h6 : ∀ r, r ∈ Set.range f → y ≤ r := h'.2

  have h7 : ∃ t, f t = x := by
    simpa using h3

  rcases h7 with ⟨t, ht⟩

  have h11 : ∃ a, f a = y := by
    simpa using h5

  rcases h11 with ⟨a, ha⟩

  have h12 : f (-t) = 2 - x := by
    linarith [ht, h2 t]

  have h13 : y ≤ 2 - x := by
    have hx : f (-t) ∈ Set.range f := by
      simp
    have hx2 : y ≤ f (-t) := by
      apply h6
      exact hx
    linarith [h12]

  have h14 : f (-a) = 2 - y := by
    linarith [ha, h2 a]

  have h15 : x ≥ 2 - y := by
    have hx : f (-a) ∈ Set.range f := by
      simp
    have hx2 : f (-a) ≤ x := by
      apply h4
      exact hx
    linarith [h14]

  linarith [h13, h15]