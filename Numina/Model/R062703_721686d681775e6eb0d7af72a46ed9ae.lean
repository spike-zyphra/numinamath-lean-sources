import Mathlib

theorem number_theory_256866 (x : ℤ) :
    5 * x + 2 ≡ 0 [ZMOD 17] ↔ ∃ k, x = 3 + 17 * k := by 
  constructor
  · -- Proof of the first direction: If 5x + 2 ≡ 0 (mod 17), then there exists integer k such that x = 3 + 17k
    intro h
    norm_num [Int.ModEq] at h 
    have h1 : (5 * x + 2) % 17 = 0 := by 
      omega 
    have h2 : x % 17 = 3 := by 
      omega 
    refine ⟨(x - 3) / 17, by omega⟩ 
  · -- Proof of the second direction: If there exists integer k such that x = 3 + 17k, then 5x + 2 ≡ 0 (mod 17)
    rintro ⟨k, rfl⟩ 
    norm_num [Int.ModEq]
    all_goals 
      ring_nf 
      <;> omega