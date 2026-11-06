import Mathlib

theorem number_theory_2110
    (a b : ℤ)
    (c : ℚ)
    (ha : IsLeast {x | 0 ≤ x} a)
    (hb : IsGreatest {x | x < 0} b)
    (hc : ∀ x : ℚ, |x| < |c| → x = c) :
    a - b + c = 1 := by
  have ha2 : a = 0 := by
    have h1 : 0 ≤ a := by
      have h2 : a ∈ ({x | 0 ≤ x} : Set ℤ) := by
        exact ha.left
      simpa using h2
    have h3 : ∀ x : ℤ, 0 ≤ x → a ≤ x := by
      have h4 : ∀ x ∈ ({x | 0 ≤ x} : Set ℤ), a ≤ x := by
        apply ha.right
      intro x hx
      have hx2 : x ∈ ({x | 0 ≤ x} : Set ℤ) := by
        simpa using hx
      exact h4 x hx2
    have h4 := h3 0 (by norm_num)
    omega
  have hb2 : b = -1 := by
    have h1 : b < 0 := by
      have h2 : b ∈ ({x | x < 0} : Set ℤ) := by
        exact hb.left
      simpa using h2
    have h3 : ∀ x : ℤ, x < 0 → x ≤ b := by
      have h4 : ∀ x ∈ ({x | x < 0} : Set ℤ), x ≤ b := by
        apply hb.right
      intro x hx
      have hx2 : x ∈ ({x | x < 0} : Set ℤ) := by
        simpa using hx
      exact h4 x hx2
    have h4 := h3 (-1) (by norm_num)
    omega
  have hc2 : c = 0 := by
    by_cases h : c = 0
    · exact h
    · -- Assume h : c ≠ 0
      -- Then we can show |c| > 0
      have h1 : |c| > 0 := by
        have h2 : c ≠ 0 := h
        exact abs_pos.mpr h2
      -- We need to prove |-c / 2| < |c|
      -- First, establish |-c / 2| = |c| / 2
      have h3 : |-c / 2| = |c| / 2 := by
        have h4 : |-c / 2| = |(-c / 2 : ℚ)| := by
          rfl
        have h5 : |(-c / 2 : ℚ)| = |(-c : ℚ) / (2 : ℚ)| := by
          ring_nf
        have h6 : |(-c : ℚ) / (2 : ℚ)| = |(-c : ℚ)| / |(2 : ℚ)| := by
          apply abs_div
        have h7 : |(-c : ℚ)| = |c| := by
          apply abs_neg
        have h8 : |(2 : ℚ)| = (2 : ℚ) := by
          norm_num [abs_of_pos]
        rw [h4, h5, h6, h7, h8]
        all_goals omega
      -- Now, explicitly state that |c| / 2 < |c|
      have h3' : |c| / 2 < |c| := by
        have h4 : |c| > 0 := h1
        have h5 : |c| / 2 < |c| := by
          have h6 : 0 < (|c| : ℚ) := by
            exact_mod_cast h4
          have h7 : (|c| : ℚ) > 0 := by
            exact h6
          have h4' : (|c| : ℚ) / 2 < (|c| : ℚ) := by
            linarith
          have h6 : (|c| : ℚ) / 2 < (|c| : ℚ) := by
            linarith
          exact_mod_cast h4'
        exact h5
      -- Use these results to show |-c / 2| < |c|
      have h4 : |-c / 2| < |c| := by
        rw [h3]
        exact_mod_cast h3'
      have h5 : (-c / 2 : ℚ) = c := by
        apply hc (-c / 2)
        exact h4
      have h6 : (-c / 2 : ℚ) * 2 = c * (2 : ℚ) := by
        rw [h5]
        all_goals ring_nf
      have h7 : (-c : ℚ) = 2 * c := by
        have h8 : (-c / 2 : ℚ) * 2 = -c := by
          ring_nf
        linarith [h6, h8]
      -- Hence 3c = 0
      have h8 : (3 * c : ℚ) = 0 := by
        linarith [h7]
      -- Therefore c = 0
      have h9 : (c : ℚ) = 0 := by
        linarith [h8]
      contradiction
  rw [ha2, hb2, hc2]
  norm_num
  <;> tauto
  <;> omega
  all_goals try { tauto <;> omega }
  all_goals try { tauto <;> omega }
  all_goals try { tauto <;> omega }
  all_goals try { tauto <;> omega }
  all_goals try { tauto <;> omega }