import Mathlib

theorem number_theory_6180 (x : ℕ) (hx : x ∈ Finset.Icc 100 999) (h : 4 * x ≡ 11 [MOD 17]) :
    Even x → x ≤ 976 := by
  intro hx_even
  rw [Finset.mem_Icc] at hx
  rcases hx with ⟨hx100, hx999⟩
  norm_num [Nat.ModEq] at h
  by_contra h1
  push_neg at h1
  have h2 : x > 976 := h1
  have h3 : x ≤ 999 := hx999
  interval_cases x <;> try { contradiction }
  <;> norm_num at h hx_even <;> omega