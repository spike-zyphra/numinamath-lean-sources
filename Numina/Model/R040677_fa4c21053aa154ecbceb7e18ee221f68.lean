import Mathlib

theorem algebra_22346:
    ∃(r : Finset ℝ), r = {w | ∃(f : ℝ → ℝ), f 1 = 1 ∧ 
        (∀ x y z, f (x + f (y + z)) + f (f (x + y) + z) = 2 * y) ∧ 
        w = f 5 } ∧ 
    r.card * r.sum id = -3 := by
  use {-3}
  constructor
  · -- Show that r = {w | ...}
    ext w
    simp 
    constructor
    · -- Show that -3 is in the set
      intro hw
      rw [hw]
      use (fun x => -x + 2)
      constructor
      · -- Check that f 1 = 1
        norm_num 
      constructor
      · -- Check the functional equation
        intro x y z 
        simp [add_assoc]
        all_goals 
          ring 
      · -- Check that -3 = f 5
        norm_num 
    · -- Assume w is in the set, prove w = -3
      rintro ⟨f, hf1, hfx, hw⟩
      have h1 : ∀ x y z, f (x + f (y + z)) + f (f (x + y) + z) = 2 * y := by
        intro x y z 
        specialize hfx x y z 
        simpa using hfx 
      have h2 : ∀ t, f (f t) = t := by
        intro t 
        have eq1 := h1 0 t 0
        simp at eq1 
        have eq2 : f (f t) = t := by 
          linarith 
        exact eq2 
      have h3 : ∀ y z, f (f y + z) = y - z := by 
        intro y z 
        have eq1 := h1 0 y z 
        have eq2 : f (f (y + z)) = y + z := by 
          apply h2 
        simp at eq1 
        linarith [eq1, eq2] 
      have h4 : ∀ y w, f w = y - (w - f y) := by
        intro y w 
        have eq1 := h3 y (w - f y) 
        have eq5 : f y + (w - f y) = w := by 
          linarith 
        rw [eq5] at eq1 
        linarith 
      have h6 : ∀ y, f y = -y + 2 := by 
        intro y 
        have eq1 := h4 y 0 
        have eq2 := h4 1 0 
        have hf0 : f 0 = 2 := by 
          have eq3 : f 1 = f 0 - 1 := by 
            linarith 
          linarith [hf1] 
        have eq4 : f y = -y + 2 := by 
          linarith [hf0]
        exact eq4 
      have h7 : w = -3 := by 
        rw [hw] 
        have h8 : f 5 = -3 := by
          rw [h6 5]
          norm_num
        linarith 
      linarith 
  · -- Show that r.card * r.sum id = -3 
    norm_num