import Mathlib

/-
2. (BEL 4) From a bag containing 5 pairs of socks, each pair a different color, a random sample of 4 single socks is drawn. Any complete pairs in the sample are discarded and replaced by a new pair draw from the bag. The process continues until the bag is empty or there are 4 socks of different colors held outside the bag. What is the probability of the latter alternative?
-/
theorem socks_problem (p1 p2 p3 : ℚ) 
(p1def : p1 = (↑(Nat.choose 5 4) * 2^4) / (↑(Nat.choose 10 4) : ℚ))
(p2def : p2 = (5 * ↑(Nat.choose 4 2) * 2^2) / (↑(Nat.choose 10 4) : ℚ))
(p3def : p3 = (4 : ℚ) / (↑(Nat.choose 6 2) : ℚ))
:
  p1 + p2 * p3 = 8/15 := by {
    
    /- The only way to arrive at the latter alternative is to draw four different socks in the first drawing 
       or to draw only one pair in the first drawing and then draw two different socks in the last drawing. 
       We will call these probabilities respectively p₁, p₂, p₃. -/

    /- Compute p₁: The probability of drawing four different socks in the first draw. -/
    have hp1 : p1 = 8 / 21 := by
      have t1 : Nat.choose 5 4 = 5 := by norm_num
      have t2 : Nat.choose 10 4 = 210 := by {
        aesop
      }
      rw [p1def, t1, t2]
      norm_num

    /- Compute p₂: The probability of drawing exactly one pair and two other single socks in the first draw. -/
    have hp2 : p2 = 4 / 7 := by
      have t1 : Nat.choose 4 2 = 6 := by aesop
      have t2 : Nat.choose 10 4 = 210 := by aesop
      rw [p2def, t1, t2]
      norm_num

    /- Compute p₃: The probability of drawing two different socks in the final draw, given that a pair was drawn initially. -/
    have hp3 : p3 = 4 / 15 := by
      have t1 : Nat.choose 6 2 = 15 := by aesop
      rw [p3def, t1]
      norm_num

    /- We finally calculate the desired probability: P = p₁ + p₂ * p₃ = 8/15. -/
    rw [hp1, hp2, hp3]
    norm_num
  }
