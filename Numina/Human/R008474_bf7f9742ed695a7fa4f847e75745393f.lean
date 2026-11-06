import Mathlib

/- The increasing sequence $1,3,4,9,10,12,13\cdots$ consists of all those positive integers which are powers of 3 or sums of distinct powers of 3. Find the $100^{\mbox{th}}$ term of this sequence.
 -/
theorem number_theory_13385 (s : ℕ → ℕ)
    (hs: ∀n, s n = (Nat.digits 2 n).foldr (fun a b ↦ b * 3 + a) 0) :
    s 100 = 981 := by
  rw [hs 100]
  norm_num
