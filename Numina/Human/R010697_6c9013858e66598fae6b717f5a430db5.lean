import Mathlib

/- The real numbers $x,y,z,w$ satisfy $2x+y+z+w=1$, $x+3y+z+w=2$, $x+y+4z+w=3$, $x+y+z+5w=25$. Find the value of w. -/
theorem algebra_610976 (x y z w : ℝ) (h₁ : 2 * x + y + z + w = 1) (h₂ : x + 3 * y + z + w = 2) (h₃ : x + y + 4 * z + w = 3) (h₄ : x + y + z + 5 * w = 25) : w = (11:ℝ) / 2 := by
  --Multiplying the four equations by $12,6,4,3$ respectively, we get $24x+12y+12z+12w=12$ $6x+18y+6z+6w=12$ $4x+4y+16z+4w=12$ $3x+3y+3z+15w=75$. Adding these yields $37 x+37 y+37 z+37 w=111$.
  have h₅ : 37 * x + 37 * y + 37 * z + 37 * w = 111 := by
    calc
      37 * x + 37 * y + 37 * z + 37 * w = (24 * x + 12 * y + 12 * z + 12 * w) + (6 * x + 18 * y + 6 * z + 6 * w) + (4 * x + 4 * y + 16 * z + 4 * w) + (3 * x + 3 * y + 3 * z + 15 * w):= by ring
      _ = 12 * (2 * x + y + z + w) + 6 * (x + 3 * y + z + w) + 4 * (x + y + 4 * z + w) + 3 * (x + y + z + 5 * w) := by ring
      _ = 12 * 1 + 6 * 2 + 4 * 3 + 3 * 25 := by rw [h₁,h₂,h₃,h₄]
      _ = 111 := by norm_num
  --Dividing both sides by $37$, we get $x+y+z+w=3$.
  have h₆ : x + y + z + w = 3 := by linarith only [h₅]
  --Subtract this from the fourth given equation to obtain $4 w=22$, or $w=\boxed{\frac{11}{2}}$.
  have h₇ : w = (11:ℝ) / 2 := by 
    calc
      w = (4 * w) / 4 := by ring
      _ = (x + y + z + 5 * w - (x + y + z + w)) / 4 := by ring
      _ = (25 - 3) / 4 := by rw[h₄, h₆]
      _ = 11 / 2 := by norm_num
  exact h₇