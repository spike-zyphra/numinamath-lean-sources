import Mathlib

/-On my ping-pong team there are four times as many right-handed boys as left-handed boys.  Of the students on the team who are left-handed, there are twice as many girls as there are boys.  Half of the girls who are on the team are left-handed.  If there are 36 people on the team, how many are right-handed boys? (Assume no player plays ping-pong equally well with both hands.)-/
theorem algebra_19941 {right_boy left_boy left_girl right_girl : ℕ}
    (h₀ : right_boy = 4 * left_boy) (h₁ : left_girl = 2 * left_boy)
    (h₂ : right_girl + left_girl = 2 * left_girl)
    (h₃ : right_boy + left_boy + left_girl + right_girl = 36) :
    right_boy = 16 := by linarith
