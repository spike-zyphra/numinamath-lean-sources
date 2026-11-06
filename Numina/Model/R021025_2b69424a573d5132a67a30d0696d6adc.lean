import Mathlib

theorem algebra_229786 {x : ℂ} (hx : x^2 + x + 1 = 0) :
    x^14 + 1 / x^14 = -1 := by
  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    norm_num at hx
  
  have h2 : x^2 = -x - 1 := by
    have eq1 : x^2 + x + 1 = 0 := hx
    calc
      x^2 = x^2 + x + 1 - x - 1 := by ring
      _ = 0 - x - 1 := by rw [eq1]
      _ = -x - 1 := by ring
  
  have h3 : x^3 = 1 := by
    calc
      x^3 = x * x^2 := by ring_nf
      _ = x * (-x -1) := by rw [h2]
      _ = -x^2 -x := by ring_nf
      _ = -(-x -1) - x := by rw [h2]
      _ = x + 1 - x := by ring_nf
      _ = 1 := by ring_nf
  
  have h4 : x^14 = x^2 := by
    calc
      x^14 = (x^3) ^ 4 * x^2 := by ring_nf
      _ = 1 ^ 4 * x^2 := by rw [h3]
      _ = x^2 := by ring_nf
  
  have h5 : 1 / x^14 = x := by
    rw [h4]
    have h6 : 1 / x^2 = x := by
      field_simp [h1]
      <;> rw [← h3]
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h6]
  
  have h6 : (x ^ 14 + 1 / x ^ 14) = -1 := by
    rw [h5, h4]
    rw [h2]
    have eq1 : (-x - 1 + x) = -1 := by
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> tauto
    simpa using eq1
  exact h6
  all_goals
    ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num
    <;> nlinarith
    <;> nlinarith