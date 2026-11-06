import Mathlib

theorem number_theory_6853 (x : ℤ) : 256*x≡179[ZMOD 337] ↔ x≡81[ZMOD 337]:= by
  apply Iff.intro
  · -- Assume 256x ≡ 179 (mod 337), prove x ≡ 81 (mod 337)
    intro h
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- Assume x ≡ 81 (mod 337), prove 256x ≡ 179 (mod 337)
    intro h
    norm_num [Int.ModEq] at h ⊢
    omega