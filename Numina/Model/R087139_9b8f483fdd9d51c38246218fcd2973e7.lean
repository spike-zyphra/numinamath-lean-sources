import Mathlib

theorem number_theory_13362 {x : ℕ} (hx : x ∈ Finset.Icc 100 999) (h1 : x ≡ 4 [MOD 5]) (h2 : x ≡ 7 [MOD 9]) (h3 : x ≡ 15 [MOD 19]) : x = 889 := by
  rw [Finset.mem_Icc] at hx
  rcases hx with ⟨hx1, hx2⟩
  norm_num [Nat.ModEq] at h1 h2 h3
  interval_cases x <;> omega