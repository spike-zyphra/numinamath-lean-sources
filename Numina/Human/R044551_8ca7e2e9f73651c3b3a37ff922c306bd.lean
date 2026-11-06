import Mathlib

/- Determine the range of the function $y = -\cos^2 x + \sin x$. -/
theorem algebra_8991 : Set.range (-Real.cos ^ 2 + Real.sin) = {y |-5/4 ≤ y ∧  y ≤ 1} := by
ext y
constructor
-- mp direction. find the range of the function
intro hy
simp at hy
simp
rcases hy with ⟨x,hx⟩
let z := Real.sin x
have z_def: z = Real.sin x := rfl
have h1: -(Real.cos x) ^ 2 + Real.sin x = (z + 1/2)^2 - 5/4 := by
  rw [z_def]
  have: (Real.cos x)^2 = 1 - (Real.sin x)^2 := Real.cos_sq' x
  rw [this]
  ring
rw [h1] at hx
-- the function is transformed into y = (sinx+1/2)^2 - 5/4
-- since -1 ≤ sinx ≤ 1, -1/2 ≤ sinx+1/2 ≤ 3/2, range of (sinx+1/2)^2 is determined, therefore range of the whole y is determined.  
have y_lower: -5/4 ≤ y := by
  rw [← hx]
  have ht1: 0 ≤ (z+1/2)^2 := sq_nonneg (z+1/2)
  have ht2: 0 - 5/4 ≤ (z+1/2)^2 - 5/4 := by exact tsub_le_tsub_right ht1 (5 / 4)
  have: (0:ℝ) - 5/4 = (-5/4:ℝ) := by ring
  rwa [this] at ht2
have y_upper: y ≤ 1 := by
  rw [← hx]
  have h1: (z + 1 / 2) ^ 2 ≤ 9/4 := by
    have h1: |z+1/2| ≤ 3/2 := by
      rw [abs_le]
      have ht1: -(3 / 2) ≤ z + 1 / 2 := by
        have: z ≥ -1 := by
          rw [z_def]
          exact Real.neg_one_le_sin x
        linarith [this]
      have ht2: z + 1 / 2 ≤ 3 / 2 := by
        have: z ≤ 1 := by exact Real.sin_le_one x
        linarith [this]
      exact ⟨ht1,ht2⟩
    have: (9/4:ℝ) = (3/2)^2 := by norm_num
    rw [this]
    have: (3/2:ℝ) = |(3/2:ℝ)| := by
      have: 0 ≤ (3/2:ℝ) := by norm_num
      exact Eq.symm (abs_of_nonneg this)
    rw [this] at h1
    apply sq_le_sq.mpr h1
  linarith [h1]
exact ⟨y_lower, y_upper⟩
-- mpr direction. given the function f(x), find value of that x
intro hy
simp at hy
simp
have y1nonneg: 0 ≤ y+(5/4:ℝ) := by
  have: (-5/4:ℝ) ≤ y := hy.left
  linarith [this]
-- in the mp direction, we prove y = (sinx+1/2)^2 -5/4.
-- so y+5/4 = sinx+1/2, and solve the equation, sinx = ±√(y+5/4-1/2)
-- we choose x = √(y+5/4-1/2) here, the negative one is also ok.
use (Real.arcsin (Real.sqrt (y+5/4) - 1/2))
have: Real.cos (Real.arcsin (√(y + 5 / 4) - 1 / 2)) ^ 2 = 1 - Real.sin (Real.arcsin (√(y + 5 / 4) - 1 / 2)) ^ 2 := by
  exact Real.cos_sq' (Real.arcsin (√(y + 5 / 4) - 1 / 2))
rw [this]
have: -(1 - Real.sin (Real.arcsin (√(y + 5 / 4) - 1 / 2)) ^ 2) = Real.sin (Real.arcsin (√(y + 5 / 4) - 1 / 2)) ^ 2 - 1 := by simp
rw [this]
have: Real.sin (Real.arcsin (√(y + 5 / 4) - 1 / 2)) =  (√(y + 5 / 4) - 1 / 2) := by
  have h1: -1 ≤ √(y + 5 / 4) - 1 / 2 := by
    have: 0 ≤ √(y + 5 / 4) := Real.sqrt_nonneg (y + 5 / 4)
    linarith [this]
  have h2: √(y + 5 / 4) - 1 / 2 ≤ 1 := by
    have ht1: (y + 5 / 4) ≤ 1 + 5/4 := by
      linarith [hy.right]
    have: 1 + 5/4 = (1+1/2 :ℝ)^2 := by norm_num
    rw [this] at ht1
    have ht2: Real.sqrt (y + 5 / 4) ≤ Real.sqrt ((1+1/2: ℝ)^2) := by
      apply Real.sqrt_le_sqrt ht1
    have: √((1 + 1 / 2) ^ 2) = (1+1/2:ℝ) := by
      ring
      have h11: (9:ℝ) = 3*3 := by norm_num
      have h22: (4:ℝ) = 2*2 := by norm_num
      rw [h11, h22]
      simp
    rw [this] at ht2
    linarith [ht2]
  apply Real.sin_arcsin h1 h2
repeat rw [this]
ring_nf
have: Real.sqrt (5 / 4 + y) ^ 2 = (5/4:ℝ)+y := by
  rw [add_comm]
  exact Real.sq_sqrt y1nonneg
rw [this]
ring