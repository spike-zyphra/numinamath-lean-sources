import Mathlib

theorem algebra_12949 (f g : ℝ → ℝ)
    (hf : f = fun x => 3 * x ^ 2 + 4 * x - 5) (hg : g = fun x => x ^ 2 + 11) :
    {(x, y) : ℝ × ℝ | y = f x ∧ y = g x} =
    {(-4, 27), (2, 15)} := by 
  ext ⟨x, y⟩
  simp [hf, hg]
  constructor
  · -- First, we show that if (x, y) is in the intersection set, then (x, y) ∈ {(-4, 27), (2, 15)}
    rintro ⟨h₁, h₂⟩
    have h3 : 2 * x ^ 2 + 4 * x - 16 = 0 := by 
      linarith 
    have h4 : x ^ 2 + 2 * x - 8 = 0 := by 
      nlinarith 
    have h5 : (x + 4) * (x - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case 1: x + 4 = 0, so x = -4
      have hx : x = -4 := by linarith 
      have hy : y = 27 := by 
        nlinarith 
      left 
      exact ⟨hx, hy⟩ 
    · -- Case 2: x - 2 = 0, so x = 2
      have hx : x = 2 := by linarith 
      have hy : y = 15 := by 
        nlinarith 
      right 
      exact ⟨hx, hy⟩ 
  · -- Now, we show the reverse: If (x, y) ∈ {(-4, 27), (2, 15)}, then it is in the intersection set
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- For (-4, 27)
      constructor <;> norm_num 
    · -- For (2, 15)
      constructor <;> norm_num