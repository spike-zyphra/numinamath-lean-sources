import Mathlib

/-What is the smallest possible integer value of $x$ if $12\div(x+1)$ is an integer?-/
theorem algebra_19923 : IsLeast {x : ℤ | 12 % (x + 1) = 0} (-13) := by
  simp [IsLeast, lowerBounds]
  -- show that natAbs (n + 1) ≤ 12
  intro n hn
  apply Int.natAbs_le_of_dvd_ne_zero at hn
  simp [Int.natAbs] at hn
  -- suppose m = n + 1
  set m := n + 1 with hm
  -- consider the type of m
  match m with
  -- case 1 : m ∈ ℕ
  |  Int.ofNat m =>
    simp at hn
    have h : 0 ≤ n + 1 := by rw [<-hm]; simp
    linarith only [h]
  -- case 2 : m < 0
  | Int.negSucc m =>
    simp at hn
    -- show that Int.negSucc m ≥ -12
    have h : -12 ≤ Int.negSucc m := by
      rw [Int.negSucc_coe]
      norm_num
      exact hn
    -- substitute the Int.negSucc m
    rw [hm] at h
    linarith only [h]