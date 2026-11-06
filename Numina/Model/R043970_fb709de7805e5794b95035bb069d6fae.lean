import Mathlib

open Real

theorem algebra_175962 : √(8 + √60) - √(7 + √40) = √(7 - √40) - √(8 - √60) := by
  have h1 : (√5 + √3)^2 = 8 + √60 := by
    calc (√5 + √3)^2
      _ = √5^2 + 2*√5*√3 + √3^2 := by rw [add_sq]
      _ = 5 + 2*√5*√3 + √3^2    := by rw [sq_sqrt]; linarith
      _ = 5 + 2*√5*√3 + 3       := by rw [sq_sqrt]; linarith
      _ = 8 + 2*√5*√3           := by linarith
      _ = 8 + √2^2*√5*√3        := by rw [sq_sqrt]; linarith
      _ = 8 + √2*√2*√(5*3)      := by rw [mul_assoc, sqrt_mul] <;> linarith
      _ = 8 + √(2*2)*√(5*3)     := by rw [← sqrt_mul]; linarith
      _ = 8 + √4*√(5*3)         := by ring
      _ = 8 + √4*√15            := by ring_nf
      _ = 8 + √(4*15)           := by rw [← sqrt_mul]; linarith
      _ = 8 + √60               := by ring_nf

  have h2 : (√5 - √3)^2 = 8 - √60 := by
    calc (√5 - √3)^2
      _ = √5^2 - 2*√5*√3 + √3^2 := by rw [sub_sq]
      _ = 5 - 2*√5*√3 + √3^2    := by rw [sq_sqrt]; linarith
      _ = 5 - 2*√5*√3 + 3       := by rw [sq_sqrt]; linarith
      _ = 8 - 2*√5*√3           := by linarith
      _ = 8 - √2^2*√5*√3        := by rw [sq_sqrt]; linarith
      _ = 8 - √2*√2*√(5*3)      := by rw [mul_assoc, sqrt_mul] <;> linarith
      _ = 8 - √(2*2)*√(5*3)     := by rw [← sqrt_mul]; linarith
      _ = 8 - √4*√(5*3)         := by ring
      _ = 8 - √4*√15            := by ring_nf
      _ = 8 - √(4*15)           := by rw [← sqrt_mul]; linarith
      _ = 8 - √60               := by ring_nf

  have h3 : (√5 + √2)^2 = 7 + √40 := by
    calc (√5 + √2)^2
      _ = √5^2 + 2*√5*√2 + √2^2 := by rw [add_sq]
      _ = 5 + 2*√5*√2 + √2^2    := by rw [sq_sqrt]; linarith
      _ = 5 + 2*√5*√2 + 2       := by rw [sq_sqrt]; linarith
      _ = 7 + 2*√5*√2           := by linarith
      _ = 7 + √2^2*√5*√2        := by rw [sq_sqrt]; linarith
      _ = 7 + √2*√2*√(5*2)      := by rw [mul_assoc, sqrt_mul] <;> linarith
      _ = 7 + √(2*2)*√(5*2)     := by rw [← sqrt_mul]; linarith
      _ = 7 + √4*√(5*2)         := by ring
      _ = 7 + √4*√10            := by ring_nf
      _ = 7 + √(4*10)           := by rw [← sqrt_mul]; linarith
      _ = 7 + √40               := by ring_nf

  have h4 : (√5 - √2)^2 = 7 - √40 := by
    calc (√5 - √2)^2
      _ = √5^2 - 2*√5*√2 + √2^2 := by rw [sub_sq]
      _ = 5 - 2*√5*√2 + √2^2    := by rw [sq_sqrt]; linarith
      _ = 5 - 2*√5*√2 + 2       := by rw [sq_sqrt]; linarith
      _ = 7 - 2*√5*√2           := by linarith
      _ = 7 - √2^2*√5*√2        := by rw [sq_sqrt]; linarith
      _ = 7 - √2*√2*√(5*2)      := by rw [mul_assoc, sqrt_mul] <;> linarith
      _ = 7 - √(2*2)*√(5*2)     := by rw [← sqrt_mul]; linarith
      _ = 7 - √4*√(5*2)         := by ring
      _ = 7 - √4*√10            := by ring_nf
      _ = 7 - √(4*10)           := by rw [← sqrt_mul]; linarith
      _ = 7 - √40               := by ring_nf

  have : 0 ≤ √5 - √2 := by
    suffices √2 ≤ √5 by linarith
    apply sqrt_le_sqrt
    linarith

  have : 0 ≤ √5 - √3 := by
    suffices √3 ≤ √5 by linarith
    apply sqrt_le_sqrt
    linarith

  have h2' : √(8 - √60) = √5 - √3 := by
    have : 8 - √60 = (√5 - √3)^2 := by linarith [h2]
    rw [this, sqrt_sq]
    linarith

  have h4' : √(7 - √40) = √5 - √2 := by
    have h5_nonneg : 0 ≤ √5 - √2 := by
      have h51 : √2 ≤ √5 := Real.sqrt_le_sqrt (by norm_num)
      linarith [h51]
    have h6 : (√5 - √2) ^ 2 = 7 - √40 := by linarith [h4]
    have h7 : √(7 - √40) = √5 - √2 := by
      have h8 : (7 - √40 : ℝ) = (√5 - √2) ^ 2 := by linarith [h6]
      rw [h8]
      rw [Real.sqrt_sq (show 0 ≤ √5 - √2 by linarith [h5_nonneg] ) ]
    exact h7

  have h1' : √(8 + √60) = √5 + √3 := by
    have : 8 + √60 = (√5 + √3)^2 := by linarith [h1]
    rw [this, sqrt_sq]
    positivity

  have h3' : √(7 + √40) = √5 + √2 := by
    have : 7 + √40 = (√5 + √2)^2 := by linarith [h3]
    rw [this, sqrt_sq]
    positivity
  rw [h1', h3', h4', h2']
  ring