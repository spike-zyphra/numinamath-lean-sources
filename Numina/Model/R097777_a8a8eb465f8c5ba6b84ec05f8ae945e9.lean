import Mathlib

theorem algebra_167018 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1)
    (h1 : x * 30 + y * 10 + z * 15 = 40) (h2 : x * 70 + y * 90 + z * 25 = 60) :
    y ∈ Set.Icc 40 43 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  constructor
  all_goals
    nlinarith