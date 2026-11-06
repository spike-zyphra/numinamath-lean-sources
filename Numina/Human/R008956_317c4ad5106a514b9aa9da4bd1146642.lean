import Mathlib

/- Xiao Gang's house is 900 meters away from his school. He walks with a step length of 0.45 meters. How many steps can Xiao Gang take from his house to his school? (Set up an equation to solve the problem)-/
theorem algebra_9404 (d : ℝ) (h : d = 900) (l : ℝ) (hl : l = 0.45) :
    d / l = 2000 := by
  -- Let's denote the number of steps Xiao Gang can take from his house to his school as $x$.
  -- We can set up the equation:
  -- $0.45x = 900$
  -- Now, we solve for $x$:
  -- $x = \frac{900}{0.45}$
  -- $x = 2000$
  -- ## Answer
  -- $\boxed{2000 \text{ steps}}$
  -- So, Xiao Gang can take 2000 steps from his house to his school.
  norm_num [h, hl]
