import Mathlib

theorem number_theory_305984 (x1 x2 x3 x4 x5: ℕ) (h1: 0 < x1) (h2: x1 < x2) (h3: x2 < x3) (h4: x3 < x4) (h5: x4 < x5)
(o1: Odd x1) (o2: Odd x2) (o3: Odd x3) (o4: Odd x4) (o5: Odd x5)
  (h: x1 + x2 + x3 + x4 + x5 = 85):
  21 ≤ x5 ∧ x5 ≤ 69 := by

  -- Prove that the numbers must have minimal values
  -- First, prove lower bounds for x5
  -- Since x1 < x2 < x3 < x4 < x5 and they are all odd 
  -- The minimum difference between each is 2
  -- This implies x5 >= 21

  -- From the inequalities
  have h6 : x1 ≥ 1 := by
    omega

  have h6' : x2 ≥ x1 + 1 := by
    omega

  have h7 : x3 ≥ x2 + 1 := by
    omega

  have h8 : x4 ≥ x3 + 1 := by
    omega

  have h9 : x5 ≥ x4 + 1 := by
    omega

  have h10 : x1 % 2 = 1 := by
    obtain ⟨k, hk⟩ := o1
    omega

  have h11 : x2 % 2 = 1 := by
    obtain ⟨k, hk⟩ := o2
    omega

  have h12 : x3 % 2 = 1 := by
    obtain ⟨k, hk⟩ := o3
    omega

  have h13 : x4 % 2 = 1 := by
    obtain ⟨k, hk⟩ := o4
    omega

  have h14 : x5 % 2 = 1 := by
    obtain ⟨k, hk⟩ := o5
    omega

  have h15 : x2 ≥ x1 + 2 := by 
    omega

  have h16 : x3 ≥ x2 + 2 := by 
    omega

  have h17 : x4 ≥ x3 + 2 := by
    omega

  have h18 : x5 ≥ x4 + 2 := by
    omega

  -- Calculate the lower bound for x5
  have h19 : x5 ≥ 21 := by 
    omega

  have h20 : x5 ≤ 69 := by 
    -- Calculating the upper bound
    nlinarith

  constructor
  · omega
  · omega