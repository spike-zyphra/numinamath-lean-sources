import Mathlib

theorem algebra_22531 :
    IsGreatest {a | ∃ (x:ℝ) (y:ℝ) , x ∈ Set.Icc (-5) (-3) ∧ y ∈ Set.Icc 2 4 ∧ a = (x + y) / (x - y)}  (3 / 7) := by 
  constructor
  · -- Show that 3/7 is in the set
    use -5, 2
    norm_num [Set.mem_Icc]
  · -- Show that 3/7 is the greatest in the set
    intro a ha
    rcases ha with ⟨x, y, hx, hy, ha⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : x - y < 0 := by
      nlinarith
    have h2 : (x + y) / (x - y) ≤ 3 / 7 := by
      apply (div_le_iff_of_neg' (by linarith)).mpr 
      linarith 
    linarith