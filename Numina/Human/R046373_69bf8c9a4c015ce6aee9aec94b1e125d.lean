import Mathlib

/- James writes down three integers. Alex picks some two of those integers, takes the average of them,
 and adds the result to the third integer. If the possible final results Alex could get are 42, 13, and 37,
 what are the three integers James originally chose? -/
theorem algebra_609445 (x y z : ℤ) (h₁: (x + y: ℝ) / 2 + z = 42) 
    (h₂ : (y + z: ℝ) / 2 + x = 13) (h₃ : (x + z: ℝ) / 2 + y = 37) :
    x = -20 ∧ y = 28 ∧ z = 38 := by
  -- Adding these three equations yields $2(x+y+z)=92$, 
  have hsum : (x + y + z : ℝ) = 46 := by linarith [h₁, h₂, h₃]
  -- so $\frac{x+y}{2}+z=23+\frac{z}{2}=42$ so $z=38$. 
  have : (x + y: ℝ) / 2 + z = (x + y + z: ℝ) / 2 + (z: ℝ) / 2 := by ring
  rw [this, hsum] at h₁
  have hz : z = (38: ℝ) := by linarith [h₁]
  -- Similarly, $x=-20$ and $y=28$.
  have : (y + z: ℝ) / 2 + x = (x + y + z: ℝ) / 2 + (x: ℝ) / 2 := by ring
  rw [this, hsum] at h₂
  have hx : x = (-20: ℝ) := by linarith [h₂]
  have : (x + z: ℝ) / 2 + y = (x + y + z: ℝ) / 2 + (y: ℝ) / 2 := by ring
  rw [this, hsum] at h₃
  have hy : y = (28: ℝ) := by linarith [h₃]
  exact ⟨by norm_cast at hx, by norm_cast at hy, by norm_cast at hz⟩
