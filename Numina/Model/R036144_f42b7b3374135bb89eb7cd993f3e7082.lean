import Mathlib

theorem algebra_10232 {f g : ℝ → ℝ} (hf : f = fun x => 3 * x - 2) (hg : g = fun x => f (f (f (f x)))) :
    g '' Set.Icc 0 2 = Set.Icc (-80) 82 := by
  have h1 : g = fun x => 81 * x - 80 := by
    rw [hg]
    funext x
    simp [hf]
    ring
  rw [h1]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First direction: if y in image, in the interval
    rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hx2⟩
    constructor
    · -- Show -80 ≤ 81 * x - 80
      linarith
    · -- Show 81 * x - 80 ≤ 82
      linarith
  · -- Second direction: if in interval, in image
    rintro ⟨hy1, hy2⟩
    use (y + 80) / 81
    constructor
    · -- Show x ∈ [0, 2]
      constructor
      · -- Show x ≥ 0
        linarith
      · -- Show x ≤ 2
        linarith
    · -- Show that 81 * x - 80 = y
      field_simp
      <;> linarith