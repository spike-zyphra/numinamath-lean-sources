import Mathlib

theorem algebra_270421 (d c s : ℝ) (hd : d > 0) (hc : c > 0) (hs : s > 0) :
    {x : ℝ | x / s = d / c + (d - x) / s} = {(c + s) * d / (2 * c)} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x / s = d / c + (d - x) / s, prove x = (c + s) * d / (2 * c)
    intro h
    have h1 : x / s - (d - x) / s = d / c := by linarith 
    have h2 : x / s - (d - x) / s = (2 * x - d) / s := by
      field_simp [(show s ≠ 0 by linarith)]
      <;> ring 
    rw [h2] at h1 
    have h3 : c * (2 * x - d) = s * d := by
      have h4 : s ≠ 0 := by linarith 
      have h5 : c ≠ 0 := by linarith 
      field_simp [h4, h5] at h1 ⊢ 
      nlinarith 
    have h4 : x = (c + s) * d / (2 * c) := by 
      have h5 : c ≠ 0 := by linarith 
      field_simp [h5] at h3 ⊢ 
      nlinarith 
    exact h4 
  · -- Assume x = (c + s) * d / (2 * c), prove x / s = d / c + (d - x) / s
    intro h
    rw [h]
    have h5 : c ≠ 0 := by linarith
    have h6 : s ≠ 0 := by linarith
    field_simp [h5, h6]
    <;> ring