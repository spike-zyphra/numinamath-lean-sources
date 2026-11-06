import Mathlib

/- A non-square rectangle has integer dimensions. The number of square units in its area is numerically equal to the number of units in its perimeter. What is the number of units in the perimeter of this rectangle? -/
theorem algebra_13960 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (harea : a * b = 2 * (a + b)) :
    2 * (a + b) = 18 := by
  -- We are given that the area equals the perimeter: a * b = 2 * (a + b)
  have h : a * b - 2 * a - 2 * b = 0 := by linarith
  -- Rewrite the equation: a * b - 2 * a - 2 * b = 0 as (a - 2) * (b - 2) = 4
  have h_factor : (a - 2) * (b - 2) = 4 := by
    linarith
  -- Solving the equation (a - 2) * (b - 2) = 4 for integers a and b
  let solutions := [(-4, -1), (-2, -2), (-1, -4), (1, 4), (2, 2), (4, 1)]
  -- Consider only positive integer solutions for a, b
  let res : List (ℤ × ℤ) := (Int.range (-4) 5).product (Int.range (-4) 5)|>.filter (fun (a, b) => a * b = 4)
  have heq : res = solutions := by decide
  have : (a - 2, b - 2) ∈ solutions := by
    simp [← heq, res, h_factor]
    have ha' : a - 2 ∣ 4 := Dvd.intro _ h_factor
    have hb' : b - 2 ∣ 4 := by
      use a - 2; rw [← h_factor, mul_comm]
    constructor 
    · rw [Int.mem_range_iff, ← Int.le_sub_one_iff, show (5 : ℤ) - 1 = 4 by norm_num]
      constructor
      linarith
      exact Int.le_of_dvd (by norm_num) ha'
    · rw [Int.mem_range_iff, ← Int.le_sub_one_iff, show (5 : ℤ) - 1 = 4 by norm_num]
      constructor
      linarith
      exact Int.le_of_dvd (by norm_num) hb'
  -- Thus, $a, b$ pairs are $(3, 6)$ and $(6, 3)$, respectively.
  have : (a, b) = (3, 6) ∨ (a, b) = (6, 3) := by
    simp [solutions] at this
    rcases this with (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    all_goals try simp [sub_eq_iff_eq_add] at ha hb
    all_goals try linarith
    left
    simp [ha, hb]
    rw [← hb] at ha
    exfalso
    exact hne ha
    right
    simp [ha, hb]
  -- For both pairs, the perimeter $2(a + b) = 2(3 + 6) = 18$.
  rcases this with (h | h)
  · simp at h
    obtain ⟨ha, hb⟩ := h
    rw [ha, hb]
    norm_num
  · simp at h
    obtain ⟨ha, hb⟩ := h
    rw [ha, hb]
    norm_num