import Mathlib

theorem number_theory_95972 {x y m : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : y = Nat.ofDigits 10 [x % 10, x / 10]) (hm : m > 0) (h : x ^ 2 - y ^ 2 = m ^ 2) :
    x + y + m = 154 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with  ⟨hy1, hy2⟩
  simp [Nat.ofDigits, List.foldl] at hxy
  have h1 : y = x := by
    omega
  have h4 : x ^ 2 - y ^ 2 = 0 := by
    rw [show y = x by omega]
    all_goals
      omega
  have h6 : m ^ 2 = 0 := by
    omega
  have h7 : m = 0 := by
    nlinarith
  linarith