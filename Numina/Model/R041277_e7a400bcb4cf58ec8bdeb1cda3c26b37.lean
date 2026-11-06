import Mathlib

theorem algebra_136455 (f : ℝ → ℝ) (hf : ∀ x, x ≠ 2/3 → 2 * x / (3 * x - 2) ≠ 2/3 → 2 * f x + f (2 * x / (3 * x - 2)) = 996 * x) :
    ∀ x, x ≠ 2 / 3 → f x = 1992 * x * (x - 1) / (3 * x - 2) := by
  intro x hx
  have h1 : x ≠ 2 / 3 := hx
  have h2 : 3 * x - 2 ≠ 0 := by
    intro h
    apply h1
    linarith
  let y := 2 * x / (3 * x - 2)
  have h3 : y ≠ 2 / 3 := by
    by_contra h
    have h4 : 2 * x / (3 * x - 2) = 2 / 3 := by
      simpa [y] using h
    have h5 : 6 * x = 2 * (3 * x - 2) := by
      have h6 : 3 * x - 2 ≠ 0 := h2
      field_simp at h4
      linarith
    linarith
  have h4 : 2 * f x + f y = 996 * x := by
    specialize hf x h1 (by
      have h6 : 2 * x / (3 * x - 2) ≠ 2/3 := h3
      tauto
    )
    simpa [y] using hf

  have h5 : 2 * f y + f x = 996 * y := by
    have h6 : y ≠ 2/3 := h3
    have h7 : 2 * y / (3 * y - 2) = x := by
      have h8 : 3 * x - 2 ≠ 0 := h2
      field_simp [show y = 2 * x / (3 * x - 2) by rfl, h8]
      <;> ring_nf
    have h8 : 2 * f y + f x = 996 * y := by
      specialize hf y h3 (by
        have h6 : 2 * y / (3 * y - 2) = x := h7
        have h7' : 2 * y / (3 * y - 2) ≠ 2/3 := by
          intro h
          rw [show 2 * y / (3 * y - 2) = x by linarith [h7]] at h
          have h6' : x = 2/3 := by linarith
          exfalso
          apply h1
          linarith
        tauto
      )
      rw [h7] at hf
      linarith
    linarith

  have eq1 : f x = 664 * x - 332 * y := by
    linarith [h4, h5]

  rw [eq1]
  have eq2 : y = 2 * x / (3 * x - 2) := by
    rfl
  rw [eq2]
  have h6 : 3 * x - 2 ≠ 0 := h2
  field_simp
  ring_nf