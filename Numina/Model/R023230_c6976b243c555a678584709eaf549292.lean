import Mathlib

theorem number_theory_6174 (m : ℕ) (hm : m > 2) :
    ¬(∀ n ∈ Finset.Icc 0 (m - 1), ∃! i, i^2 ≡ n [ZMOD m]) := by
  intro h
  have h1 := h 1 (by 
    have h2 : m ≥ 3 := by linarith
    have h3 : 1 ≤ m - 1 := by 
      omega
    simp at *
    all_goals omega 
  )
  rcases h1 with ⟨x, ⟨h2, h3⟩⟩ 
  have hx15 : (1 : ℤ) ^ 2 ≡ (1 : ℤ) [ZMOD m] := by 
    simp [Int.ModEq] 
  have hx11 : (1 : ℤ) = x := by 
    apply h3 
    exact hx15 
  have hx13 : (1 : ℤ) = x := hx11 
  have hx21 : (-1 : ℤ) ^ 2 ≡ (1 : ℤ) [ZMOD m] := by 
    simp [Int.ModEq] 
  have hx24 : (-1 : ℤ) = (1 : ℤ) := by 
    have h13 : (-1 : ℤ) = x := by 
      apply h3 
      exact hx21 
    rw [show x = (1 : ℤ) by linarith [hx11]] at h13 
    linarith 
  have hx20 : m ≤ 2 := by 
    have h9 : m > 2 := by exact_mod_cast hm 
    have hx24' : (-1 : ℤ) = (1 : ℤ) := hx24 
    omega 
  omega