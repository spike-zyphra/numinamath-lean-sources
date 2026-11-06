import Mathlib

theorem algebra_21379 : IsGreatest {dist : ℝ | ∃ d : ℕ → ℝ, dist = d 48 - d 47 ∧ d 41 = 0 ∧ d 50 = 100 ∧ (∀ i, d (i + 1) ≥ d i + 6)} 52 := by
  constructor
  · -- we verify that there exists a possible solution.
    use fun i => if i ≤ 47 then (i - 41) * (6 : ℝ) else (88 : ℝ) + (i - 48) * (6 : ℝ)
    norm_num
    <;> aesop
    all_goals try { linarith }
    all_goals try { aesop }
  · -- Now we need to show that no larger value than 52 can be achieved
    intro a
    rintro ⟨d, hdist, h41, h50, h⟩
    have h42 : d 42 ≥ d 41 + 6 := h 41
    have h43 : d 43 ≥ d 42 + 6 := h 42
    have h44 : d 44 ≥ d 43 + 6 := h 43
    have h45 : d 45 ≥ d 44 + 6 := h 44
    have h46 : d 46 ≥ d 45 + 6 := h 45
    have h47 : d 47 ≥ d 46 + 6 := h 46
    have h48 : d 48 ≥ d 47 + 6 := h 47
    have h49 : d 49 ≥ d 48 + 6 := h 48
    have h50' : d 50 ≥ d 49 + 6 := h 49
    -- So we have
    -- d(41) = 0
    -- d(42) >= 0+6 =6
    -- d(43) >= 6+6 =12
    -- d(44) >=12+6 =18
    -- d(45) >=18+6 =24
    -- d(46) >=24+6 =30
    -- d(47) >=30+6 =36
    -- d(48) >=36+6 =42
    -- d(49) >=42+6 =48
    -- d(50) >=48+6 =54

    -- But we have that d(50) =100, so this additional distance can
    -- be assigned to the exit 49
    -- But we need to maximize exit 47 to 48
    -- From h50': 100 >= d 49 + 6
    -- So d 49 <= 94
    -- From h49: d 49 >= d 48 + 6
    -- We get that d 48 <= 88

    -- From h47: d 47 >= 36
    -- and from h48: d48 >= 42
    -- then the distance from 47 to 48: d48 - d47 <= 88 - 36 = 52
    rw [hdist]
    linarith