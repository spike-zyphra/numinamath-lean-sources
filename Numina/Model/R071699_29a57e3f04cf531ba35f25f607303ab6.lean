import Mathlib

theorem algebra_265231 (k : ℤ) (h : ∃ a d, 36 + k = a^2 ∧ 300 + k = (a + d)^2 ∧ 596 + k = (a + 2 * d)^2) :
    k = 925 := by
  rcases h with ⟨a, d, h1, h2, h3⟩
  have eq1 : (a + d)^2 - a^2 = 264 := by 
    nlinarith 
  have eq2 : (a + d)^2 - a^2 = (2 * a + d) * d := by 
    ring
  rw [eq2] at eq1
  -- Similarly, subtract the second and third equations:
  -- From h3 - h2: (596 + k) - (300 + k) = (a + 2d)^2 - (a + d)^2
  -- This simplifies to: 296 = (a + 2d)^2 - (a + d)^2 = (a + 2d + a + d)(d) = (2a + 3d) * d
  have eq3 : (a + 2 * d)^2 - (a + d)^2 = 296 := by 
    nlinarith 
  have eq4 : (a + 2 * d)^2 - (a + d)^2 = (2 * a + 3 * d) * d := by 
    ring
  rw [eq4] at eq3
  -- Subtracting these two equations:
  -- From eq3 - eq1: 2d^2 = 32
  -- Therefore: d^2 = 16
  -- Then: d = 4 or d = -4
  have eq5 : 2 * d ^ 2 = 32 := by 
    nlinarith 
  -- From 2d² = 32, we get d²= 16
  -- Therefore, |d|=4, so d=4 or d=-4
  have h4 : d ^ 2 = 16 := by 
    linarith 
  have h5 : d = 4 ∨ d = -4 := by 
    have h : d ^ 2 = 16 := h4
    have : d = 4 ∨ d = -4 := by 
      have h1 : d ≤ 4 := by nlinarith
      have h2 : -4 ≤ d := by nlinarith
      interval_cases d <;> tauto
    tauto 
  rcases h5 with (h5 | h5)
  · -- Case d = 4
    have ha1 : 2 * a + 4 = 66 := by 
      nlinarith [h5]
    -- So 2a + 4 = 66, then 2a = 62, a = 31
    have ha2 : a = 31 := by 
      linarith 
    -- From a = 31 and k + 36 = a²:
    -- k + 36 = 31² = 961, so k = 961 - 36 = 925
    nlinarith [ha2, h5]
  · -- Case d = -4
    have ha1 : 2 * a + (-4) = -66 := by 
      nlinarith [h5]
    -- Solving 2a - 4 = -66: 2a = -62, a = -31
    have ha2 : a = -31 := by 
      linarith 
    -- Check k + 36 = a²: k + 36 = (-31)² = 961, k = 925
    nlinarith [ha2, h5]