import Mathlib



theorem algebra_9440 {x y : ℤ} {z : ℚ}
    (hx : IsLeast {u | 0 < u} x)
    (hy : IsGreatest {u | u < 0} y)
    (hz : IsLeast {|u| | u : ℚ} z):
    2 * x + 3 * y + 4 * z = -1 := by
  have hx1 : x = 1 := by
    have h1 : x > 0 := by 
      have h1 : x ∈ ({u | 0 < u}) := by
        exact hx.1
      simpa using h1
    have h2 : ∀ u : ℤ, (0 < u) → x ≤ u := by 
      apply hx.2
    have h3 : x ≤ 1 := by 
      specialize h2 1 (by norm_num)
      linarith
    have h4 : x ≥ 1 := by
      omega 
    linarith
  have hy1 : y = -1 := by
    have h1 : y < 0 := by 
      have h1 : y ∈ ({u | u < 0}) := by
        exact hy.1
      simpa using h1
    have h2 : ∀ u : ℤ, (u < 0) → u ≤ y := by 
      apply hy.2
    have h3 : -1 ≤ y := by 
      specialize h2 (-1) (by norm_num)
      linarith
    have h4 : y ≤ -1 := by
      omega
    linarith
  have h1 : z = (0 : ℚ) := by 
    have h3 : z ≤ (0 : ℚ) := by 
      have h4 : (0 : ℚ) ∈ ({ |u| | u : ℚ }) := by
        use (0 : ℚ)
        all_goals norm_num
      have h5 : z ≤ (0 : ℚ) := by 
        apply hz.2 
        exact h4 
      linarith 
    have h4 : 0 ≤ z := by
      have h5 : z ∈ ({ |u| | u : ℚ }) := hz.1
      rcases h5 with ⟨u, hu⟩
      have h6 : z = |(u : ℚ)| := by 
        linarith [hu]
      rw [h6]
      apply abs_nonneg 
    linarith
  rw [hx1, hy1, h1]
  norm_num