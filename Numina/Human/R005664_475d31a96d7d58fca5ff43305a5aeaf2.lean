import Mathlib

/-Carl is on a vertex of a regular pentagon. Every minute, he randomly selects an adjacent vertex (each with probability $\frac{1}{2}$ ) and walks along the edge to it. What is the probability that after 10 minutes, he ends up where he had started?
-/

open Nat Finset

def successfuk_walks := 
  -- The sum of (choose 10 k) over all k from 0 to 10...
  (range 11).sum (fun k => 
  -- ...such that the final position is the start.
  if (2 * k - 10 : ℤ) % 5 = 0 then choose 10 k else 0)

lemma successful_walks_eq : successfuk_walks
    = choose 10 0 + choose 10 5 + choose 10 10 := by
  unfold successfuk_walks  
  have h_equiv : ∀ k : ℕ, ((2 * k - 10 : ℤ) % 5 = 0 ↔ k % 5 = 0) := by
    intro k
    omega
    
  simp [h_equiv]
  decide

theorem combinatorics_609313 :
  successfuk_walks / (2^10 : ℚ) = 127 / 512 := by
  unfold successfuk_walks
  simp [successful_walks_eq]
  norm_num
  native_decide

