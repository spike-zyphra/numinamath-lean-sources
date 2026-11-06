import Mathlib

theorem algebra_311590 (x y z a b c : ℝ)
    (h₀ : a = -x^2 + y * z - 1 / 2011)
    (h₁ : b = -y^2 + x * z - 1 / 2011)
    (h₂ : c = -z^2 + x * y - 1 / 2011) :
    min (min a b) c < 0 := by 
  by_contra h
  have h4 : min (min a b) c ≥ 0 := by
    linarith
  have ha : a ≥ 0 := by
    have h3 : (min (min a b) c) ≤ a := by
      simp [min_le_iff]
      all_goals
      try { nlinarith }
      all_goals
      try { tauto }
    nlinarith
  have hb : b ≥ 0 := by
    have h4 : (min (min a b) c) ≤ b := by
      simp [min_le_iff]
      all_goals
      try { nlinarith }
      all_goals
      try { tauto }
    nlinarith
  have hc : c ≥ 0 := by
    have h5 : (min (min a b) c) ≤ c := by
      simp [min_le_iff]
      all_goals
      try { nlinarith }
      all_goals
      try { tauto }
    nlinarith
  have h5 : a + b + c = -x^2 -y^2 -z^2 + (y * z + x * z + x * y) - 3 / 2011 := by 
    rw [h₀, h₁, h₂]
    ring
  have h6 : a + b + c < 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y + y * z + z * x), sq_nonneg (x * y * z)]
  have h7 : a + b + c ≥ 0 := by 
    nlinarith
  linarith