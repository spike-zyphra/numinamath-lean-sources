import Mathlib

/-Let $n$ be a positive even integer. Find the remainder when $24^n - 15^n$ is divided by 13. Show the answer is 0.-/
theorem Number_Theory_635749 (n : ℕ) (hn : Even n) :
  (24^n - 15^n) % 13 = 0 := by
  obtain⟨k,hk⟩:=even_iff_two_dvd.mp hn
  -- Substituting n = 2k, we get 24^(2k) - 15^(2k) = (24²)^k - (15²)^k = 576^k - 225^k
  simp[hk,pow_mul]
  -- The key insight: 576 ≡ 225 (mod 13), so their powers are also congruent modulo 13
  have: (576 ^ k) %13 = (225 ^ k) %13  := by
    refine (ZMod.natCast_eq_natCast_iff' (576 ^ k) (225 ^ k) 13).mp ?_
    simp
    congr
  exact Nat.sub_mod_eq_zero_of_mod_eq this
