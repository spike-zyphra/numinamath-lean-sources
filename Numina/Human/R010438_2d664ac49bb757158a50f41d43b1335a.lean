import Mathlib

/-At Beaumont High School, there are 20 players on the basketball team.  All 20 players are taking at least one of biology or chemistry.  (Biology and chemistry are two different science courses at the school.)  If there are 8 players taking biology and 4 players are taking both sciences, how many players are taking chemistry?-/
theorem algebra_14790 {bio chem both : ℕ} (h1 : bio = 8)
  (h2 : both = 4) (h3 : bio + chem - both = 20) :
  chem = 16 := by
    -- 8 players are taking biology, so $20 - 8 = 12$ players are not taking biology, which means 12 players are taking chemistry alone.
    -- Since 4 are taking both, there are $12 + 4 = \boxed{16}$ players taking chemistry.
    rw [h1, h2, Nat.sub_add_comm (by omega)] at h3
    linarith
