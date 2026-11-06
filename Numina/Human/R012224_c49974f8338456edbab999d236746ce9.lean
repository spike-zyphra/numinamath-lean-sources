import Mathlib

/- Prove that for every integer $n\ge  3$ there are such positives integers $x$ and $y$ such that $2^n = 7x^2 + y^2$ -/

theorem number_theory_91314 (n : ℕ) (hn : 3 ≤ n) :
∃ x y : ℤ, 0 < x ∧ 0 < y ∧ 2^n = 7 * x^2 + y^2 := by 

  --We divide into two cases: even n and odd n
  have : Even n ∨ Odd n := by exact Nat.even_or_odd n
  rcases this with evenn | oddn

  --For even n = 2k. Let x= 2^(k-2) and y = 3*2^(k-2).
  obtain ⟨k,hk⟩ := evenn
  have : 2 ≤ k := by omega
  use 2^(k-2), 3*2^(k-2)
  simp [hk]
  ring_nf
  have : (k * 2) = (k-2)*2 + 4 := by omega
  rw [this]
  rw [pow_add]
  norm_num

  --For odd n = 2k+1. Let x= 2^(k-1) and y = 2^(k-1).
  obtain ⟨k,hk⟩ := oddn
  have : 1 ≤ k := by omega
  use 2^(k-1), 2^(k-1)
  simp [hk]
  ring_nf
  have : (k * 2) = (k-1)*2 + 2 := by omega
  rw [this]
  rw [pow_add]
  norm_num
  ring
