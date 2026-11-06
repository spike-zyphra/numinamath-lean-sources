import Mathlib

theorem number_theory_93334
    (s : Set ℕ) (hs : s = {y : ℕ | ∃ b r g n, n = b + r + g + y ∧ 3 * b = n ∧ 4 * r = n ∧ g = 6}) :
    IsLeast s 4 := by 
  rw [hs]
  constructor
  · -- Show that 4 is in s
    use 8  -- b = 8
    use 6  -- r = 6
    use 6  -- g = 6
    use 24  -- n = 24
    all_goals norm_num
    all_goals omega
  · -- Show that 4 is the smallest element in s
    intro y hy
    rcases  hy with ⟨b, r, g, n, hn_eq, hb_eq, hr_eq, hg_eq⟩
    omega
  all_goals omega
  all_goals norm_num
  <;> omega
  all_goals tauto
  all_goals norm_num
  all_goals omega